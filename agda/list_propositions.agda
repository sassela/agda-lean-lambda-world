module agda.list_propositions where
open import agda.dependent_types

infixl 6  _∸_
infixl 7  _*_

private
  variable
    A : Set

-- -----

-- There are some Agda commands that may help in interactive proving. These are:
-- c-C + c-U + c-C + c-, ---> show the goal of the hole having the cursor
-- c-C + c-C             ---> split by cases with respect to a variable
-- c-C + c-space         ---> check and fill a hole with the expression provided


data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _++_

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

data _∈_ {A : Set} : A → List A → Set where
  here  : {x : A} {xs : List A} → x ∈ (x ∷ xs)
  there : {x y : A} {xs : List A} → y ∈ xs → y ∈ (x ∷ xs)

in1 : "a" ∈ ("a" ∷ "b" ∷ "c" ∷ "d" ∷ "e" ∷ [])
in1 = here

in2 : "d" ∈ ("a" ∷ "b" ∷ "c" ∷ "d" ∷ "e" ∷ [])
in2 = there (there (there (here)))

data Either (A B : Set) : Set where
  i1 : A → Either A B
  i2 : B → Either A B

ei-++ : {a : A} {xs ys : List A} → Either (a ∈ xs) (a ∈ ys) → a ∈ (xs ++ ys)
ei-++ = {!   !}

++-ei : {a : A} {xs ys : List A} → a ∈ (xs ++ ys) → Either (a ∈ xs) (a ∈ ys)
++-ei = {!   !}

-- -----

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

-- -----

*-1 : (m : ℕ) → (suc zero) * m ≡ m
*-1 = {!   !}

-- -----

*-0 : (m : ℕ) → m * zero ≡ zero
*-0 = {!   !}

-- -----

*-suc : (m n : ℕ) → m * (suc n) ≡ m * n + m
*-suc = {!   !}

-- -----

*-comm : (m n : ℕ) → m * n ≡ n * m
*-comm = {!   !}