{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS -Wall -fno-warn-missing-signatures #-}

module Main where

import           Control.Monad.Trans.Except
import           LLVM.General.AST.Global
import LLVM.General
import LLVM.General.Context
import           Control.Monad hiding (void)
import           Control.Monad.Free.TH
import           Control.Monad.State hiding (void)
import           Data.Word
import           LLVM.General.AST hiding (type')
import           LLVM.General.AST.IntegerPredicate
import           LLVM.General.AST.Type
import           Prelude hiding (EQ, fst, snd)
import Control.Monad.Free
import qualified LLVM.General.AST.Constant as Const
-- import Debug.Trace

data St = St{ unique :: Word, label :: Name, instrs :: [Named Instruction], blocks :: [BasicBlock] }

type O a = StateT St IO a

newtype E a = E{ unE :: Expr } deriving (Show, Eq)

data Expr
  = VWord Word
  | VName Type Name
  | Op Op [Expr]
  deriving (Show, Eq)
           
data Op
  = ADD
  | SUB
  | MUL
  | UDIV
  | UREM
  | SHL
  | LSHR
  | AND
  | OR
  | XOR
  | Eq
  | Ne
  | UGt
  | UGe
  | ULt
  | ULe
  | Idx
  | Fst
  | Snd
  deriving (Show, Eq)

data Func a
  = Ret_ (Maybe Expr)
  | Alloca_ Type (Name -> a)
  | Load_ Expr (Name -> a)
  | Store_ Expr Expr a
  | Switch_ Expr [Name] a
  | Br_ Name a
  | Label_ Name a
  | GenLabel_ (Name -> a)
  deriving (Functor)
  
type M a = Free Func a

makeFree ''Func

tt = do
  bb <- runM foo
--  print bb
  runJit defaultModule{ moduleDefinitions = [ GlobalDefinition functionDefaults{ name = Name "main", returnType = void, parameters = ([], False), basicBlocks = bb } ] }

{-
main = tt
tt = runJit defaultModule{ moduleDefinitions = map GlobalDefinition [globalVariableDefaults{ name = UnName 55, type' = i32 }, f, g ] }
  where
    f = functionDefaults{ name = UnName 0, returnType = void, parameters = ([], False), basicBlocks = [] }
    g = functionDefaults
      { name = UnName 0
      , returnType = i32
      , parameters = ([], False)
      , basicBlocks = [BasicBlock (UnName 5) []                                                                                        (Do $ Ret (Just $ cint32 42) []) ] }
      
newtype Addr = Addr{ unAddr :: Word } deriving (Show, Eq)

-}

liftExcept :: ExceptT String IO a -> IO a
liftExcept = runExceptT >=> either fail return

runJit x = do
  withContext $ \cxt -> liftExcept $ withModuleFromAST cxt x $ \m -> do
    s <- moduleLLVMAssembly m
    putStrLn s

terminate :: (InstructionMetadata -> Terminator) -> O ()
terminate f = do
  modify $ \st -> st
    { label = error "label"
    , instrs = []
    , blocks = BasicBlock (label st) (reverse $ instrs st) (Do $ f []) : blocks st
    }

runM :: M () -> IO [BasicBlock]
runM m = liftM (reverse . blocks) $ flip execStateT (St 0 (Name "start") [] []) $ iterM runFunc (m >> ret_ Nothing)

runFunc :: Func (O ()) -> O ()
runFunc x = case x of
  Ret_ Nothing -> terminate $ Ret Nothing
  Ret_ (Just a) -> do
    oa <- genOperand a
    terminate $ Ret $ Just oa
  Alloca_ t f -> do
    v <- instr $ Alloca t Nothing 0
    f v
  Load_ a f -> do
    oa <- genOperand a
    v <- instr $ Load False oa Nothing 0
    f v
  Store_ a b c -> do
    oa <- genOperand a
    ob <- genOperand b
    instr_ $ Do $ Store False oa ob Nothing 0 []
    c
  Br_ a b -> do
    terminate $ Br a
    b
  Switch_ a bs c -> do
    oa <- genOperand a
    terminate $ Switch oa (last bs) $ zip (map (Const.Int 32) [0 ..]) $ init bs
    c
  GenLabel_ a -> genName >>= a
  Label_ a b -> do
    modify $ \st -> st{ label = a }
    b
    
data Ptr a

switch :: E Word -> [M ()] -> M ()
switch x ys = do
  ns <- mapM (const genLabel_) ys
  ne <- genLabel_
  
  switch_ (unE x) ns

  let
    f :: (Name, M ()) -> M ()
    f (n,y) = do
      label_ n
      y
      br_ ne

  mapM_ f $ zip ns ys

  label_ ne

new_ x = new x >>= load

new :: E a -> M (E (Ptr a))
new x = do
  n <- alloca_ t
  let v = E $ VName (ptr t) n
  store v x
  return v
  where
    t = typeofE x

data Array a
data Tuple a b

fst :: E (Ptr (Tuple a b)) -> E (Ptr a)
fst = unop Fst

snd :: E (Ptr (Tuple a b)) -> E (Ptr b)
snd = unop Snd

idx :: E (Ptr (Array a)) -> E Word -> E (Ptr a)
idx = binop Idx

tuple :: E a -> E b -> M (E (Ptr (Tuple a b)))
tuple x y = do
  n <- alloca_ t
  let v = E $ VName (ptr t) n
  store (fst v) x
  store (snd v) y
  return v
  where
    t = StructureType False [typeofE x, typeofE y]
  
array :: [E a] -> M (E (Ptr (Array a)))
array [] = error "empty array"
array xs = do
  n <- alloca_ t
  let v = E $ VName (ptr t) n
-- BAL:  mapM_ (\(i,x) -> store (idx v i) x) $ zip [0 .. ] xs
  return v
  where
    t = ArrayType (fromIntegral $ length xs) $ typeofE $ head xs
  
load :: E (Ptr a) -> M (E a)
load x = liftM (E . VName t) $ load_ (unE x)
  where
    t = case typeofE x of
      PointerType a _ -> a
      asdf -> error $ "load" ++ show asdf

bar = do
  i <- new 12
  j <- load i
  switch j [ store i 33, store i 11 ]
  
foo = do
  i <- new $ w32 7
  switch 7 [ store i 42 >> store i 44, store i 22, store i 55, bar ]
  j <- load i
  store i (j .+ 7)
  t <- tuple (w32 6) (w32 7)
  j <- load $ fst t
  switch j [ store i 13, store i 55 ]
  j <- load $ snd t
  switch j [ store i 55, store i 13 ]
  arr <- array [ w32 3, 4, 5]
  store (idx arr 4) 12
  a1 <- load $ idx arr 1
  store (idx arr 1) 2
  j <- load $ idx arr 1
  switch j
    [ store (idx arr 0) 99
    , store (fst t) 12
    , store (snd t) 45
    ]
  
store :: E (Ptr a) -> E a -> M ()
store x y = store_ (unE x) (unE y)

genName :: O Name
genName = do
  u <- gets unique
  modify $ \st -> st{ unique = succ u }
  return $ UnName u

instr_ x = modify $ \st -> st{ instrs = x : instrs st }

instr f = do
  v <- genName
  instr_ $ v := f []
  return v
  
genOperand :: Expr -> O Operand
genOperand e = case e of
  VWord a -> return $ cint32 $ fromIntegral a
  VName _ n -> return $ LocalReference t n
  Op a bs -> do
    cs <- mapM genOperand bs
    v <- instr $ mkInstr a cs
    return $ LocalReference t v
  where
    t = typeofExpr e

cint32 = ConstantOperand . Const.Int 32

mkInstr :: Op -> [Operand] -> (InstructionMetadata -> Instruction)
mkInstr o args = case o of
  ADD -> g Add
  SUB -> g Sub
  MUL -> g Mul
  UDIV -> h UDiv
  UREM -> j URem
  SHL -> i Shl
  LSHR -> h LShr
  AND -> j And
  OR -> j Or
  XOR -> j Xor
  Eq -> k EQ
  Ne -> k NE
  UGt -> k UGT
  UGe -> k UGE
  ULt -> k ULT
  ULe -> k ULE
  Idx -> m y
  Fst -> m $ cint32 0
  Snd -> m $ cint32 1
  where
    g op = op True True x y
    h op = op False x y
    i op = op False False x y
    j op = op x y
    k op = ICmp op x y
    m op = GetElementPtr True x [cint32 0, op]
    x = args !! 0
    y = args !! 1
    
typeofE :: E a -> Type
typeofE = typeofExpr . unE

typeofExpr :: Expr -> Type
typeofExpr e = case e of
  VWord{} -> i32
  VName t _ -> t
  Op a bs -> case a of
    ADD -> i32
    SUB -> i32
    MUL -> i32
    UDIV -> i32
    UREM -> i32
    SHL -> i32
    LSHR -> i32
    AND -> i32
    OR -> i32
    XOR -> i32
    Eq -> i1
    Ne -> i1
    UGt -> i1
    UGe -> i1
    ULt -> i1
    ULe -> i1
    Fst -> case typeofExpr x of
      PointerType (StructureType _ [t,_]) _ -> ptr t
      _ -> error "Fst"
    Snd -> case typeofExpr x of
      PointerType (StructureType _ [_,t]) _ -> ptr t
      _ -> error "Snd"
    Idx -> case typeofExpr x of
      PointerType (ArrayType _ t) _ -> ptr t
      _ -> error "Idx"
    where
      x = bs !! 0
      
unnop :: Op -> E a -> E b
unnop o x = E $ Op o [unE x]


binop :: Op -> E a -> E b -> E c
binop o x y = E $ Op o [unE x, unE y]

unop :: Op -> E a -> E b
unop o x = E $ Op o [unE x]

infixl 6 .+
infixl 6 .-
infixl 7 .*
infixl 7 ./
infixl 7 .%
infixl 8 .<<
infixl 8 .>>
infixl 7 .&
infixl 5 .|
infixl 6 .^
infix 4 .==
infix 4 .!=
infix 4 .>
infix 4 .>=
infix 4 .<
infix 4 .<=

(.+) :: E Word -> E Word -> E Word
(.+) = binop ADD
(.-) :: E Word -> E Word -> E Word
(.-) = binop SUB
(.*) :: E Word -> E Word -> E Word
(.*) = binop MUL
(./) :: E Word -> E Word -> E Word
(./) = binop UDIV
(.%) :: E Word -> E Word -> E Word
(.%) = binop UREM
(.<<) :: E Word -> E Word -> E Word
(.<<) = binop SHL
(.>>) :: E Word -> E Word -> E Word
(.>>) = binop LSHR
(.&) :: E Word -> E Word -> E Word
(.&) = binop AND
(.|) :: E Word -> E Word -> E Word
(.|) = binop OR
(.^) :: E Word -> E Word -> E Word
(.^) = binop XOR
(.==) :: E Word -> E Word -> E Bool
(.==) = binop Eq
(.!=) :: E Word -> E Word -> E Bool
(.!=) = binop Ne
(.>) :: E Word -> E Word -> E Bool
(.>) = binop UGt
(.>=) :: E Word -> E Word -> E Bool
(.>=) = binop UGe
(.<) :: E Word -> E Word -> E Bool
(.<) = binop ULt
(.<=) :: E Word -> E Word -> E Bool
(.<=) = binop ULe

bnot :: E Word -> E Word
bnot x = negate x .- 1

w32 :: Integral a => a -> E Word
w32 = E . VWord . fromIntegral

instance Num (E Word) where
  fromInteger = w32
  negate x = 0 .- x
  abs = undefined
  signum = undefined
  (+) = undefined
  (*) = undefined

instance Enum (E Word) where
  toEnum = w32
  fromEnum (E (VWord x)) = fromIntegral x
  
