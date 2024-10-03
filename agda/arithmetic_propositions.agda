module agda.arithmetic_propositions where
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

-- -----

+-0 : (m : ℕ) → m + zero ≡ m
+-0 = ?

-- -----

+-suc : (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc = {!   !}

-- -----

+-assoc : (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc = {!   !}

-- -----

-- cong : (f : A → B) {x y} → x ≡ y → f x ≡ f y
-- cong f refl = refl

sym : {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

-- begin ... ≡⟨⟩ ... ≡⟨⟩ ... ≡⟨ xxx ⟩ ... ≡⟨⟩ ... ∎

infix  3 _∎
infixr 2 _≡⟨⟩_ step-≡
infix  1 begin_

begin_ : {x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

_≡⟨⟩_ : (x {y} : A) → x ≡ y → x ≡ y
x ≡⟨⟩ x≡y = x≡y

step-≡ : (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ x y≡z x≡y = trans x≡y y≡z

_∎ : (x : A) → x ≡ x
x ∎ = refl

syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

-- -----

+-comm : (m n : ℕ) → m + n ≡ n + m

+-comm zero n =
  begin
  n
  ≡⟨ sym (+-0 n) ⟩
  n + zero
  ∎

+-comm (suc m) n =
  begin
  suc (m + n)
  ≡⟨cong suc (+-comm m n)⟩
  suc (n + m)
  ≡⟨ sym (+-suc n m) ⟩
  n + suc m
  ∎

-- -----

+-right-comm : (m n p : ℕ) → m + n + p ≡ m + p + n
+-right-comm = {!   !}