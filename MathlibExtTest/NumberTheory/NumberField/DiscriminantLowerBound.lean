/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import MathlibExt.NumberTheory.NumberField.DiscriminantLowerBound

@[expose] public section

namespace DiscriminantLowerBoundTest

open NumberField

/-- The pure inequality at `(n, s) = (1, 0)`: the case of `ℚ`. -/
theorem middle_gt_one_zero :
    (1 / (Real.exp 1 ^ 2 * ((1 : ℕ) : ℝ))) *
        ((Real.pi * Real.exp 1 ^ 2) / 4) ^ 1
      < (((1 : ℕ) : ℝ) ^ 1 / (Nat.factorial 1 : ℝ)) ^ 2 *
          (Real.pi / 4) ^ (2 * 0) :=
  NumberField.pow_div_factorial_sq_mul_pi_div_four_pow_gt 1 0
    (by norm_num) (by norm_num)

/-- The pure inequality at `(n, s) = (2, 1)`: the totally complex
quadratic case, where the ratio of the two sides is closest to `1`. -/
theorem middle_gt_two_one :
    (1 / (Real.exp 1 ^ 2 * ((2 : ℕ) : ℝ))) *
        ((Real.pi * Real.exp 1 ^ 2) / 4) ^ 2
      < (((2 : ℕ) : ℝ) ^ 2 / (Nat.factorial 2 : ℝ)) ^ 2 *
          (Real.pi / 4) ^ (2 * 1) :=
  NumberField.pow_div_factorial_sq_mul_pi_div_four_pow_gt 2 1
    (by norm_num) (by norm_num)

/-- The pure inequality at `(n, s) = (3, 1)`: a case with `2 * s < n`,
where strictness comes from the `(π / 4)` factor. -/
theorem middle_gt_three_one :
    (1 / (Real.exp 1 ^ 2 * ((3 : ℕ) : ℝ))) *
        ((Real.pi * Real.exp 1 ^ 2) / 4) ^ 3
      < (((3 : ℕ) : ℝ) ^ 3 / (Nat.factorial 3 : ℝ)) ^ 2 *
          (Real.pi / 4) ^ (2 * 1) :=
  NumberField.pow_div_factorial_sq_mul_pi_div_four_pow_gt 3 1
    (by norm_num) (by norm_num)

/-- The pure inequality at `(n, s) = (4, 2)`: totally complex quartic,
where strictness needs the strict Stirling bound. -/
theorem middle_gt_four_two :
    (1 / (Real.exp 1 ^ 2 * ((4 : ℕ) : ℝ))) *
        ((Real.pi * Real.exp 1 ^ 2) / 4) ^ 4
      < (((4 : ℕ) : ℝ) ^ 4 / (Nat.factorial 4 : ℝ)) ^ 2 *
          (Real.pi / 4) ^ (2 * 2) :=
  NumberField.pow_div_factorial_sq_mul_pi_div_four_pow_gt 4 2
    (by norm_num) (by norm_num)

/-- Corollary 14.26 for `ℚ`: `|D_ℚ| = 1` exceeds `π / 4`. -/
theorem abs_discr_gt_exp_term_rat :
    (1 / (Real.exp 1 ^ 2 * Module.finrank ℚ ℚ)) *
      ((Real.pi * Real.exp 1 ^ 2) / 4) ^ (Module.finrank ℚ ℚ) <
        (↑|discr ℚ| : ℝ) :=
  NumberField.abs_discr_gt_exp_term ℚ

/-- Corollary 14.26 for `ℚ`, in the Minkowski-term form: the middle
term equals `1`, so the first inequality is an equality: `1 = |D_ℚ|`. -/
theorem middle_term_le_abs_discr_rat :
    (((Module.finrank ℚ ℚ : ℝ) ^ (Module.finrank ℚ ℚ) /
      (Nat.factorial (Module.finrank ℚ ℚ) : ℝ)) ^ 2 *
      (Real.pi / 4) ^ (2 * NumberField.InfinitePlace.nrComplexPlaces ℚ)) ≤
        (↑|discr ℚ| : ℝ) :=
  NumberField.middle_term_le_abs_discr ℚ

#print axioms NumberField.pow_div_factorial_sq_mul_pi_div_four_pow_gt
#print axioms NumberField.middle_term_le_abs_discr
#print axioms NumberField.abs_discr_gt_exp_term

end DiscriminantLowerBoundTest
