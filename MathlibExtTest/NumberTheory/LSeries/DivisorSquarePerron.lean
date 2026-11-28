/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.DivisorSquarePerron

/-!
# Tests for the weighted second moment of the divisor function
-/

@[expose] public section

namespace DivisorSquarePerronTest

/-- `|ζ(2)| = π²/6 ≥ 1/4`. -/
example : (1 / 4 : ℝ) ≤ ‖riemannZeta 2‖ :=
  one_div_four_le_norm_riemannZeta_of_two_le_re (by norm_num)

example : LSeriesSummable (fun n => ((ArithmeticFunction.sigma 0 n : ℕ) : ℂ) ^ 2) 2 :=
  ArithmeticFunction.LSeriesSummable_sigma_zero_sq (by norm_num)

/-- The main term is a cubic polynomial in `log x`. -/
example : ∃ P : Polynomial ℝ, P.natDegree = 3 ∧
    (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 2 * Real.log (x / n) ^ 3)
      - x * P.eval (Real.log x)) =O[Filter.atTop] fun x : ℝ => Real.sqrt x := by
  obtain ⟨P, hP, h⟩ :=
    ArithmeticFunction.exists_polynomial_degree_eq_three_sum_sigma_zero_sq_mul_log_pow_isBigO
  exact ⟨P, Polynomial.natDegree_eq_of_degree_eq_some hP, h⟩

end DivisorSquarePerronTest
