{-# LANGUAGE DeriveFunctor #-}

import qualified Data.Set as S
import Data.Set (Set)
import Control.Category
import Prelude hiding ((.), id)

newtype MemVal = MemVal Int
  deriving (Eq, Ord, Show) 

makeVal :: Int -> MemVal
makeVal n = MemVal (n `mod` 32)

getVal :: MemVal -> Int
getVal (MemVal n) = n

allVals :: [MemVal]
allVals = map makeVal [0..31]

type Addr = Int

data Instr =
  Mov Addr MemVal |
  Inc Addr |
  Dec Addr |
  Add Addr MemVal |
  Mul Addr MemVal |
  IfThenElse Pred Prog Prog |
  WhileDo Pred Prog
  deriving (Eq, Show)

newtype Prog = Prog { getInstrs :: [Instr] }
  deriving (Eq, Show)

skip :: Prog
skip = Prog []

mov :: Addr -> MemVal -> Prog
mov a v = Prog [Mov a v]

inc :: Addr -> Prog
inc a = Prog [Inc a]

dec :: Addr -> Prog
dec a = Prog [Dec a]

add :: Addr -> MemVal -> Prog
add a v = Prog [Add a v]

mul :: Addr -> MemVal -> Prog
mul a v = Prog [Mul a v]

ifThenElse :: Pred -> Prog -> Prog -> Prog
ifThenElse c p q = Prog [IfThenElse c p q]

whileDo :: Pred -> Prog -> Prog
whileDo c p = Prog [WhileDo c p]

instance Semigroup Prog where
  (<>) :: Prog -> Prog -> Prog
  (<>) (Prog xs) (Prog ys) = Prog (xs <> ys)

instance Monoid Prog where
  mempty :: Prog
  mempty  = skip
  mappend :: Prog -> Prog -> Prog
  mappend = (<>)

type State = [MemVal]

type Pred  = Set State

true :: Pred
true = S.fromList (statesOfLen 4)
  where
    statesOfLen 0 = [[]]
    statesOfLen k = [v:xs | v <- allVals, xs <- statesOfLen (k-1)]

false :: Pred
false = S.empty

newtype PT = PT { apply :: Pred -> Pred }

instance Semigroup PT where
  (<>) :: PT -> PT -> PT
  PT f <> PT g = PT (f . g) 

instance Monoid PT where
  mempty :: PT
  mempty = PT id
  mappend :: PT -> PT -> PT
  mappend = (<>)

updateAt :: Addr -> (MemVal -> MemVal) -> State -> State
updateAt _ _ [] = []
updateAt 0 f (x:xs) = f x : xs
updateAt n f (x:xs) = x : updateAt (n - 1) f xs

lfp :: (Pred -> Pred) -> Pred
lfp f = go false
  where
    go x =
      let x' = f x
      in if x' == x then x else go x'

wp :: Prog -> PT
wp (Prog instrs) = PT (\q -> foldr wpInstr q instrs)
  where
    wpInstr :: Instr -> Pred -> Pred
    wpInstr (Mov a v) q =
      S.filter (\s -> updateAt a (\_ -> v) s `S.member` q) true
    wpInstr (Inc a) q =
      S.filter (\s -> updateAt a (\x -> makeVal (getVal x + 1)) s `S.member` q) true
    wpInstr (Dec a) q =
      S.filter (\s -> updateAt a (\x -> makeVal (getVal x - 1)) s `S.member` q) true
    wpInstr (Add a v) q =
      S.filter (\s -> updateAt a (\x -> makeVal (getVal x + getVal v)) s `S.member` q) true
    wpInstr (Mul a v) q =
      S.filter (\s -> updateAt a (\x -> makeVal (getVal x * getVal v)) s `S.member` q) true
    wpInstr (IfThenElse c p r) q =
      predOr
        (predAnd c (apply (wp p) q))
        (predAnd (predNot c) (apply (wp r) q))
    wpInstr (WhileDo c p) q =
      lfp (\x ->
        predOr
          ((predNot c) `predAnd` q)
          (c `predAnd` (apply (wp p) x)))

valid :: Pred -> Prog -> Pred -> Bool
valid precon prog postcon = precon `S.isSubsetOf` apply (wp prog) postcon

predEq :: Addr -> MemVal -> Pred
predEq addr (MemVal n) = S.filter (\s -> getVal (s !! addr) == n) true

predGr :: Addr -> MemVal -> Pred
predGr addr (MemVal n) = S.filter (\s -> getVal (s !! addr) > n) true

predGrEq :: Addr -> MemVal -> Pred
predGrEq addr (MemVal n) = S.filter (\s -> getVal (s !! addr) >= n) true

predAnd :: Pred -> Pred -> Pred
predAnd p1 p2 = S.filter (\s -> s `S.member` p1 && s `S.member` p2) true

predNot :: Pred -> Pred
predNot p = S.filter (`S.notMember` p) true

predOr :: Pred -> Pred -> Pred
predOr p q = S.filter (\s -> s `S.member` p || s `S.member` q) true

pow3 :: Addr -> MemVal -> Prog
pow3 a v = mov a v <> mul a v <> mul a v

test1 :: Bool
test1 = valid precon command postcon
  where
    command = inc 0
    precon = predEq 0 (makeVal 0)
    postcon = predEq 0 (makeVal 1)

test2 :: Bool 
test2 = valid precon command postcon
  where
    command = inc 0 <> inc 0 <> inc 1 <> inc 1
    precon = predEq 0 (makeVal 0) `predAnd` predEq 1 (makeVal 0)
    postcon = predEq 0 (makeVal 2) `predAnd` predEq 1 (makeVal 2)

test3 :: Bool
test3 = valid precon command postcon
  where
    command = mov 0 (makeVal 15)
    precon = true 
    postcon = predEq 0 (makeVal 15)

test4 :: Bool
test4 = valid precon command postcon
  where
    value = (makeVal 4)
    command = mov 0 value <> mul 0 value <> mul 0 value
    precon = true
    postcon = predEq 0 (makeVal 0)

test5 :: Bool
test5 = valid precon command postcon
  where
    value = (makeVal 4)
    command = mov 0 value <> mul 0 value <> mul 0 value
    precon = predEq 0 (makeVal 10)
    postcon = predEq 0 (makeVal 0)

test6 :: Bool
test6 = valid precon command postcon
  where
    command = dec 0 <> add 0 (makeVal 10)
    precon = predEq 0 (makeVal 0)
    postcon = predEq 0 (makeVal 10)

test7 :: Bool
test7 = valid precon command postcon
  where
    command = skip <> inc 0 <> skip
    precon = predEq 0 (makeVal 0)
    postcon = predEq 0 (makeVal 1)

test8 :: Bool
test8 = valid precon command postcon
  where
    command = ifThenElse (predEq 0 (makeVal 5)) (mul 0 (makeVal 2)) skip
    precon = predEq 0 (makeVal 5)
    postcon = predEq 0 (makeVal 10)

test9 :: Bool
test9 = valid precon command postcon
  where
    command = whileDo (predGr 0 (makeVal 0)) (dec 0)
    precon = predEq 0 (makeVal 4)
    postcon = predEq 0 (makeVal 0)

test10 :: Bool
test10 = valid precon command postcon
  where
    command = whileDo true skip
    precon = predEq 0 (makeVal 4)
    postcon = predEq 0 (makeVal 0)


main :: IO ()
main = putStrLn $ show test10