/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.IntegerComplexity

@[expose] public section

open IntegerComplexity
open IntegerComplexity.Expr

-- C1-C3: explicit parenthesized expression for 6 with five ones
-- (1+1)*(1+1+1) = 2*3 = 6
def expr6 : Expr := .mul (.add .one .one) (.add (.add .one .one) .one)

example : expr6.eval = 6 := rfl
example : expr6.count = 5 := rfl

-- Required test: concrete upper bound for complexity of six
example : complexity (6 : ℕ+) ≤ 5 := by
  have h : expr6.eval = ((6 : ℕ+) : ℕ) := rfl
  exact complexity_le h

-- Required test: complexity of positive one is exactly one
example : complexity (1 : ℕ+) = 1 := complexity_one

-- Required test: public optimal-witness and minimality APIs elaborate
#check (exists_optimal : ∀ n : ℕ+, ∃ e : Expr, e.eval = (n : ℕ) ∧ e.count = complexity n)
#check (complexity_le : ∀ {n : ℕ+} {e : Expr}, e.eval = (n : ℕ) → complexity n ≤ e.count)
#check (complexity_add_le : ∀ a b : ℕ+, complexity (a + b) ≤ complexity a + complexity b)
#check (complexity_mul_le : ∀ a b : ℕ+, complexity (a * b) ≤ complexity a + complexity b)

example (n : ℕ+) : ∃ e : Expr, e.eval = (n : ℕ) ∧ e.count = complexity n :=
  exists_optimal n

example {n : ℕ+} {e : Expr} (he : e.eval = (n : ℕ)) : complexity n ≤ e.count :=
  complexity_le he
