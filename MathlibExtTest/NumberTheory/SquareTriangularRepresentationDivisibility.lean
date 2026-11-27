/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SquareTriangularRepresentationDivisibility

/-!
# Tests for prime divisibility of square and triangular representation counts
-/

open MetaMathlibExt

-- The smallest allowed p, with the even prime q.
example : (2 : ℤ) ∣ sumOfSquaresRepCount 2 3 ∧ (2 : ℤ) ∣ sumOfTriangularRepCount 2 3 :=
  prime_dvd_repCount_of_half_lt (p := 3) (q := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)

-- The two ordered triangular representations are 0 + 3 and 3 + 0.
example : sumOfTriangularRepCount 2 3 = 2 := by
  rw [sumOfTriangularRepCount, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast,
    Units.val_pow_eq_pow_val, IsUnit.unit_spec, pow_two, PowerSeries.coeff_mul]
  simp only [triangularThetaSeries, PowerSeries.coeff_mk]
  decide

-- The first odd q, with p = 2 * q - 1 just below the upper bound.
example : (3 : ℤ) ∣ sumOfSquaresRepCount 3 5 ∧ (3 : ℤ) ∣ sumOfTriangularRepCount 3 5 :=
  prime_dvd_repCount_of_half_lt (p := 5) (q := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
