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
