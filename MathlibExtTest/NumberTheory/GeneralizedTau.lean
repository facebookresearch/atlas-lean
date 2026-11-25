/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedTau

open MetaMathlibExt

-- The shifted index can itself be a multiple of the prime.
example : generalizedTau 6 3 ≡ 0 [ZMOD 3] :=
  generalizedTau_two_mul_prime_succ_modEq_zero 3 (by decide) ⟨1, rfl⟩ 2 (by decide)

-- At n = 0 the divisibility hypothesis fails and the coefficient is 1 modulo 3.
example : ¬ generalizedTau 6 1 ≡ 0 [ZMOD 3] := by
  rw [generalizedTau_one]
  decide

-- For k = -4 and n = 2, the index and the modulus share a factor.
example : 2 * generalizedTau (-4) 3 ≡ 0 [ZMOD 4] :=
  mul_generalizedTau_succ_modEq_zero 2 (by decide) (-4) (by decide)

-- At n = k = 2, the unweighted coefficient is odd.
open PowerSeries in
example : generalizedTau 2 3 = -1 := by
  change generalizedTau ((2 : ℕ) : ℤ) (2 + 1) = -1
  have h₁ : coeff 1 (pentagonalSeries ℤ) = -1 := by
    simpa [pentagonal_def] using coeff_pentagonalSeries_pentagonal ℤ 1
  have h₂ : coeff 2 (pentagonalSeries ℤ) = -1 := by
    simpa [pentagonal_def] using coeff_pentagonalSeries_pentagonal ℤ (-1)
  rw [generalizedTau_natCast 2, coeff_succ_X_mul, pow_two, coeff_mul,
    show Finset.antidiagonal (2 : ℕ) = {(0, 2), (1, 1), (2, 0)} by decide]
  simp [h₁, h₂, coeff_zero_eq_constantCoeff_apply, constantCoeff_pentagonalSeries_int]
