import Control.Arrow (Arrow)
import Distribution.PackageDescription (Condition (Var))
import Distribution.Simple (KnownExtension(FunctionalDependencies))

------------------------- Auxiliary functions

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x : xs) (y : ys)
  | x == y = x : merge xs ys
  | x <= y = x : merge xs (y : ys)
  | otherwise = y : merge (x : xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x : xs) (y : ys)
  | x < y = x : minus xs (y : ys)
  | x == y = minus xs ys
  | otherwise = minus (x : xs) ys

variables :: [Var]
variables = [[x] | x <- ['a' .. 'z']] ++ [x : show i | i <- [1 ..], x <- ['a' .. 'z']]

removeAll :: [Var] -> [Var] -> [Var]
removeAll xs ys = [x | x <- xs, not (elem x ys)]

fresh :: [Var] -> Var
fresh = head . removeAll variables

------------------------- Assignment 1: Simple types

data Type = Base | Type :-> Type
  deriving (Eq)

nice :: Type -> String
nice Base = "o"
nice (Base :-> b) = "o -> " ++ nice b
nice (a :-> b) = "(" ++ nice a ++ ") -> " ++ nice b

instance Show Type where
  show = nice

type1 :: Type
type1 = Base :-> Base

type2 :: Type
type2 = (Base :-> Base) :-> (Base :-> Base)

-- - - - - - - - - - - -- Terms

type Var = String

data Term
  = Variable Var
  | Lambda Var Type Term
  | Apply Term Term
  deriving (Eq)

pretty :: Term -> String
pretty = f 0
  where
    f i (Variable x) = x
    f i (Lambda x t m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ": " ++ nice t ++ " . " ++ f 0 m
    f i (Apply n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

instance Show Term where
  show = pretty

-- - - - - - - - - - - -- Numerals

numeral :: Int -> Term
numeral i = Lambda "f" (Base :-> Base) (Lambda "x" Base (numeral' i))
  where
    numeral' i
      | i <= 0 = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i -1))

sucterm :: Term
sucterm =
  Lambda
    "m"
    type2
    ( Lambda
        "f"
        type1
        ( Lambda
            "x"
            Base
            ( Apply
                (Apply (Variable "m") (Variable "f"))
                (Apply (Variable "f") (Variable "x"))
            )
        )
    )

addterm :: Term
addterm =
  Lambda
    "m"
    type2
    ( Lambda
        "n"
        type2
        ( Lambda
            "f"
            type1
            ( Lambda
                "x"
                Base
                ( Apply
                    (Apply (Variable "m") (Variable "f"))
                    (Apply (Apply (Variable "n") (Variable "f")) (Variable "x"))
                )
            )
        )
    )

multerm :: Term
multerm =
  Lambda
    "m"
    type2
    ( Lambda
        "n"
        type2
        ( Lambda
            "f"
            type1
            ( Apply (Variable "m") (Apply (Variable "n") (Variable "f"))
            )
        )
    )

suc :: Term -> Term
suc m = Apply sucterm m

add :: Term -> Term -> Term
add m n = Apply (Apply addterm m) n

mul :: Term -> Term -> Term
mul m n = Apply (Apply multerm m) n

example1 :: Term
example1 = suc (numeral 0)

example2 :: Term
example2 = numeral 2 `mul` (suc (numeral 2))

example3 :: Term
example3 = numeral 0 `mul` numeral 10

example4 :: Term
example4 = numeral 10 `mul` numeral 0

example5 :: Term
example5 = (numeral 2 `mul` numeral 3) `add` (numeral 5 `mul` numeral 7)

example6 :: Term
example6 = (numeral 2 `add` numeral 3) `mul` (numeral 3 `add` numeral 2)

example7 :: Term
example7 = numeral 2 `mul` (numeral 2 `mul` (numeral 2 `mul` (numeral 2 `mul` numeral 2)))

-- - - - - - - - - - - -- Renaming, substitution, beta-reduction

used :: Term -> [Var]
used (Variable x) = [x]
used (Lambda x t n) = [x] `merge` used n
used (Apply n m) = used n `merge` used m

rename :: Var -> Var -> Term -> Term
rename x y (Variable z)
  | z == x = Variable y
  | otherwise = Variable z
rename x y (Lambda z t n)
  | z == x = Lambda z t n
  | otherwise = Lambda z t (rename x y n)
rename x y (Apply n m) = Apply (rename x y n) (rename x y m)

substitute :: Var -> Term -> Term -> Term
substitute x n (Variable y)
  | x == y = n
  | otherwise = Variable y
substitute x n (Lambda y t m)
  | x == y = Lambda y t m
  | otherwise = Lambda z t (substitute x n (rename y z m))
  where
    z = fresh (used n `merge` used m `merge` [x, y])
substitute x n (Apply m p) = Apply (substitute x n m) (substitute x n p)

beta :: Term -> [Term]
beta (Apply (Lambda x t n) m) =
  [substitute x m n]
    ++ [Apply (Lambda x t n') m | n' <- beta n]
    ++ [Apply (Lambda x t n) m' | m' <- beta m]
beta (Apply n m) =
  [Apply n' m | n' <- beta n]
    ++ [Apply n m' | m' <- beta m]
beta (Lambda x t n) = [Lambda x t n' | n' <- beta n]
beta (Variable _) = []

-- - - - - - - - - - - -- Normalize

normalize :: Term -> IO ()
normalize m = do
  putStr (show (bound m))
  putStr " -- "
  print m
  let ms = beta m
  if null ms
    then return ()
    else normalize (head ms)

------------------------- Assignment 2: Type checking

type Context = [(Var, Type)]

type ArrowType = (Type, Type)

findVar :: Context -> Var -> Type
findVar [] _ = error "Variable type not found"
findVar ((y, z) : xs) x
  | y == x = z
  | otherwise = findVar xs x

extendContext :: Context -> Var -> Type -> Context
extendContext c v t = (v, t) : c

isArrow :: Type -> ArrowType
isArrow (x :-> y) = (x, y)
isArrow _ = error "not arrow type"

typeof :: Context -> Term -> Type
typeof c (Variable x) = findVar c x
typeof c (Lambda x t m) = t :-> typeof (extendContext c x t) m
typeof c (Apply n m)
  | fst (isArrow (typeof c n)) == typeof c m = snd (isArrow (typeof c n))
  | otherwise = error "no type"

example8 :: Term
example8 = Lambda "x" Base (Apply (Apply (Variable "f") (Variable "x")) (Variable "x"))

exampleA = Apply (Lambda "x" Base (Variable "x")) (Variable "y")

exampleB = Lambda "x" Base (Lambda "y" Base (Lambda "z" (Base :-> Base) (Apply (Variable "z") (Variable "x"))))

------------------------- Assignment 3: Functionals

data Functional
  = Num Int
  | Fun (Functional -> Functional)

instance Show Functional where
  show (Num i) = "Num " ++ show i
  show (Fun f) = "Fun ??"

fun :: Functional -> Functional -> Functional
fun (Fun f) = f

-- - - - - - - - - - - -- Examples
getInt:: Functional->Int
getInt (Num n) = n
getInt _ = error "Can only get int of num"



-- plussix : N -> N
plussix :: Functional
plussix = Fun addSix
  where
    addSix :: Functional -> Functional
    addSix (Num x) = Num (x + 6)
    addSix (Fun f) = error "Can't add six to a function"


plusNum :: Functional -> Functional--needs to return a function/Fun
plusNum (Num n)=  Fun plusN
  where
    plusN:: Functional -> Functional
    plusN (Num x) = Num (n+x)
    plusN _ = error " cant do that "
plusNum _  = error "can't add that"


-- plus : N -> (N -> N)
plus :: Functional
plus = Fun plusNum



twoTimes:: Functional -> Functional
twoTimes (Fun f) = Fun doTwice
  where
    doTwice :: Functional->Functional
    doTwice (Num n) = f (f(Num n))
    doTwice (Fun f) = error "Can only apply the function to a Num"
twoTimes (Num n) = error "First input must be a Fun"

--twice : (N -> N) -> N -> N
twice :: Functional
twice = Fun twoTimes

-- - - - - - - - - - - -- Constructing functionals



dummy :: Type -> Functional
dummy Base = Num 0
dummy (x :-> t) = Fun makeDummy --needs to return a funtional
  where
      makeDummy:: Functional -> Functional
      --if type of given argument is type of x  to make sure MN type matches?
      makeDummy _ = dummy t

count :: Type -> Functional -> Int
count Base (Fun f)=  getInt(f(Num 0))
count (x:-> t) (Fun f) = count t (f(dummy x)) --do the function on dummy x then do count of that
count _ (Num n) = n


increment :: Functional -> Int -> Functional
increment (Num n) i = Num (n+i)
increment (Fun f) x= Fun incrementFun
  where
    incrementFun::Functional->Functional
    incrementFun (Num y) = increment (f(Num y)) x
    incrementFun (Fun z) = increment (f(Fun z)) x



------------------------- Assignment 4 : Counting reduction steps

type Valuation = [(Var, Functional)]

findInValuation:: Valuation -> Var -> Functional
findInValuation [] _ = error "Variable type not found in Valuation"
findInValuation ((y, z) : xs) x
  | y == x = z
  | otherwise = findInValuation xs x


extendValuation :: Valuation -> Var -> Functional -> Valuation
extendValuation c x f = (x, f) : c

exampleTerm :: Term
exampleTerm = Lambda "x" Base (Lambda "y" Base (Lambda "z" (Base :-> Base) (Apply (Variable "z") (Variable "x"))))

exampleVal::Valuation
exampleVal = [("x", Num 10)]

returnValue::Functional -> Functional
returnValue (Num n) = Num n
returnValue (Fun f) = Fun f


interpret :: Context -> Valuation -> Term -> Functional
interpret c v (Variable m) = findInValuation v m

--if the Term (M) is a variable look for the variable in the valuation and return the functional
 -- this is f(g), but need to figure out how to make g work and just return f
interpret c v (Lambda x t m) = Fun someFunction
  where
    someFunction::Functional->Functional
    someFunction (Num n)= interpret (extendContext c x t) (extendValuation v x (Num n)) m
    someFunction (Fun f) = interpret (extendContext c x t) (extendValuation v x (Fun f)) m

--interpret c v (Lambda x t m) = interpret (extendContext c x t) (extendValuation v x (Fun someFunction)) m
    -- someFunction (Num n)= Num n
    -- someFunction (Fun f) = Fun f 

--The current case works if the abstraction is just the identity function, but needs to take the functional of the abstraction
--return a functional that takes N making it work as below

--if it is an abstraction 
interpret c v (Apply m n) =  increment (fun (interpret c v m) (interpret c v n)) (count (typeof c n) (interpret c v n)+1)






bound :: Term -> Int
bound t = count (typeof [] t) (interpret [] [] t)
