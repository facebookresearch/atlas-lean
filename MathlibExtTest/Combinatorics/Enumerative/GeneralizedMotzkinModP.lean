/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GeneralizedMotzkinModP

/-! # Tests for digit congruences of Laurent constant terms -/

open MetaMathlibExt LaurentPolynomial

-- Distinguish the two outer coefficients and check the constant coefficient.
example (α β γ : ℤ) :
    (linearLaurent α β γ).coeff (-1) = α ∧ (linearLaurent α β γ).coeff 0 = β ∧
      (linearLaurent α β γ).coeff 1 = γ := by
  simp only [linearLaurent, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, C_apply]
  norm_num

-- In base three, 16 is 121. The shift by one reaches the last digit 2 without a carry.
example :
    let a := fun r : ℕ => (linearLaurent 1 2 2 ^ r).coeff 0
    (a 16 + a 17 ≡ a 1 * a 2 * (a 1 + a 2) [ZMOD 3]) ∧
      (a 16 + a 17 ≡ a 5 * (a 1 + a 2) [ZMOD 3]) := by
  simpa [Finset.sum_range_succ, AddMonoidAlgebra.one_def, -single_eq_C_mul_T] using
    constantTermLinearCombination_small_last_digit 1 2 2 (by decide) (fun _ => 1)
      1 3 0 1 1 1 16 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)

-- Zero has no digits, even when the Laurent polynomial itself is zero.
example (p : ℕ) (hp : p.Prime) :
    (linearLaurent 0 0 0 ^ 0).coeff 0 ≡ 1 [ZMOD p] ∧ centralTrinomial 0 0 0 ≡ 1 [ZMOD p] := by
  simpa only [Nat.digits_zero, List.map_nil, List.prod_nil] using
    constantTerm_linearLaurent_pow_digits 0 0 0 0 0 p 0 hp

-- In base three, 11 is 102. Its digit 2 contributes the factor T₂ = 3.
example : centralTrinomial 1 1 11 ≡ 0 [ZMOD 3] := by
  have h₂ : centralTrinomial 1 1 2 = 3 :=
    congrArg (fun values : List ℤ => values[2]!) centralTrinomial_one_one_values
  refine (constantTerm_linearLaurent_pow_digits 1 1 1 1 1 3 11 (by decide)).2.trans ?_
  rw [show Nat.digits 3 11 = [2, 0, 1] by decide]
  simp [h₂, Int.ModEq]
