/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential

/-!
# Second-order Taylor remainder of `e^{ix}`

For real `x`, the remainder `R(x) = e^{ix} - 1 - ix - (ix)²/2` satisfies
`‖R(x)‖ ≤ 4 min(|x|², |x|³)` (`Complex.norm_exp_ofReal_mul_I_sub_taylor_two_le_min`),
hence `‖R(x)‖ ≤ 4|x|^{2+α}` for `0 < α < 1`
(`Complex.norm_exp_ofReal_mul_I_sub_taylor_two_le_rpow`): Lemma 1 of Section 2
(An application to the central limit theorem) in the FourierAnalysis notes.
mathlib has the first-order bound `Real.norm_exp_I_mul_ofReal_sub_one_le`.

Code-derived port of `CentralLimitTheorem.expTaylorRemainder_le_rpow` and its
helpers from `v1/Atlas/FourierAnalysis/code/CentralLimitTheorem.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`, lines 18–101, stated on the
remainder itself instead of the archived `expTaylorRemainder` wrapper. The
archived formalization and its original license/provenance remain in `v1/`
(the original license text is `v1/LICENSE`). This records equivalence to the
archived Lean statement, not verification against the printed textbook.
-/

set_option autoImplicit false

open Finset

namespace Complex

private lemma norm_ofReal_mul_I' (x : ℝ) : ‖(x * I : ℂ)‖ = |x| := by
  rw [norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs]

/-- For `|x| ≤ 1`, `‖e^{ix} - 1 - ix - (ix)²/2‖ ≤ |x|³`. -/
public theorem norm_exp_ofReal_mul_I_sub_taylor_two_le_pow_three {x : ℝ} (hx : |x| ≤ 1) :
    ‖exp (x * I) - 1 - x * I - (x * I) ^ 2 / 2‖ ≤ |x| ^ 3 := by
  have key : exp (x * I) - 1 - x * I - (x * I) ^ 2 / 2 =
      exp (x * I) - ∑ m ∈ range 3, (x * I) ^ m / (m.factorial : ℂ) := by
    simp [sum_range_succ, Nat.factorial]
    ring
  have hix : ‖(x * I : ℂ)‖ ≤ 1 := by rw [norm_ofReal_mul_I']; exact hx
  have h := exp_bound hix (n := 3) (by norm_num)
  rw [norm_ofReal_mul_I'] at h
  rw [key]
  calc _ ≤ |x| ^ 3 * ((4 : ℝ) * ((6 : ℝ) * 3)⁻¹) := h
    _ ≤ |x| ^ 3 * 1 := by gcongr; norm_num
    _ = |x| ^ 3 := mul_one _

/-- For `1 ≤ |x|`, `‖e^{ix} - 1 - ix - (ix)²/2‖ ≤ 4|x|²`. -/
public theorem norm_exp_ofReal_mul_I_sub_taylor_two_le_four_mul_sq {x : ℝ} (hx : 1 ≤ |x|) :
    ‖exp (x * I) - 1 - x * I - (x * I) ^ 2 / 2‖ ≤ 4 * |x| ^ 2 := by
  have hexp : ‖exp (x * I)‖ = 1 := norm_exp_ofReal_mul_I x
  calc _ ≤ ‖exp (x * I)‖ + ‖(1 : ℂ)‖ + ‖(x * I : ℂ)‖ + ‖((x * I) ^ 2 / 2 : ℂ)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ = 2 + |x| + |x| ^ 2 / 2 := by
        rw [hexp, norm_one, norm_ofReal_mul_I', norm_div, norm_pow, norm_ofReal_mul_I',
          norm_ofNat]
        ring
    _ ≤ 4 * |x| ^ 2 := by nlinarith [sq_nonneg (|x| - 1)]

/-- `‖e^{ix} - 1 - ix - (ix)²/2‖ ≤ 4 min(|x|², |x|³)`. -/
public theorem norm_exp_ofReal_mul_I_sub_taylor_two_le_min (x : ℝ) :
    ‖exp (x * I) - 1 - x * I - (x * I) ^ 2 / 2‖ ≤ 4 * min (|x| ^ 2) (|x| ^ 3) := by
  rcases le_total |x| 1 with hx | hx
  · rw [min_eq_right (pow_le_pow_of_le_one (abs_nonneg x) hx (by norm_num))]
    linarith [norm_exp_ofReal_mul_I_sub_taylor_two_le_pow_three hx,
      pow_nonneg (abs_nonneg x) 3]
  · rw [min_eq_left (pow_le_pow_right₀ hx (by norm_num))]
    exact norm_exp_ofReal_mul_I_sub_taylor_two_le_four_mul_sq hx

private lemma min_sq_cube_le_rpow (x : ℝ) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    min (|x| ^ 2) (|x| ^ 3) ≤ |x| ^ (2 + α) := by
  rcases le_total |x| 1 with hx | hx
  · calc min (|x| ^ 2) (|x| ^ 3) ≤ |x| ^ 3 := min_le_right _ _
      _ = |x| ^ ((3 : ℕ) : ℝ) := (Real.rpow_natCast |x| 3).symm
      _ ≤ |x| ^ (2 + α) :=
          Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg x) hx (by linarith) (by push_cast; linarith)
  · calc min (|x| ^ 2) (|x| ^ 3) ≤ |x| ^ 2 := min_le_left _ _
      _ = |x| ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast |x| 2).symm
      _ ≤ |x| ^ (2 + α) := Real.rpow_le_rpow_of_exponent_le hx (by push_cast; linarith)

/-- **Lemma 1** (Section 2, An application to the central limit theorem): for
`0 < α < 1`, `‖e^{ix} - 1 - ix - (ix)²/2‖ ≤ 4|x|^{2+α}`. -/
public theorem norm_exp_ofReal_mul_I_sub_taylor_two_le_rpow (x : ℝ) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    ‖exp (x * I) - 1 - x * I - (x * I) ^ 2 / 2‖ ≤ 4 * |x| ^ (2 + α) :=
  (norm_exp_ofReal_mul_I_sub_taylor_two_le_min x).trans
    (by gcongr; exact min_sq_cube_le_rpow x hα0 hα1)

end Complex
