/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.ExplicitFormulaContour

/-!
# Tests for the contour estimates of the explicit formulas

Instantiations of the horizontal-side bound, of moving the truncation height of a zero sum, and of
the sum over the trivial zeros.
-/

@[expose] public section

open Complex Filter Topology

namespace ExplicitFormulaContourTest

/-- The horizontal-side bound for `f σ = x^σ`, with `a = 1`, `b = 0`, `T = 1`. -/
example (x U c : ℝ) (hx : 1 < x) (hc : 0 ≤ c) (hUc : -U ≤ c) :
    ‖∫ σ in (-U)..c, ((x ^ σ : ℝ) : ℂ)‖ ≤ x ^ c * (1 / Real.log x + 0 / Real.log x ^ 2) / 1 :=
  norm_intervalIntegral_le_of_norm_le_sub_mul_rpow hx one_pos le_rfl hc hUc (by linarith)
    fun σ _ => by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) σ)]
      simp

/-- Moving the truncation height from `3` to `4` across a single point `1/2 + 7i/2`. -/
example : ‖(∑' _ : Unit, (if |((1 / 2 + 7 / 2 * I : ℂ)).im| < 3 then
        ((2 : ℝ) : ℂ) ^ (1 / 2 + 7 / 2 * I : ℂ) / (1 / 2 + 7 / 2 * I) else 0)) -
      ∑' _ : Unit, (if |((1 / 2 + 7 / 2 * I : ℂ)).im| < 4 then
        ((2 : ℝ) : ℂ) ^ (1 / 2 + 7 / 2 * I : ℂ) / (1 / 2 + 7 / 2 * I) else 0)‖ ≤
      1 * (2 / min 3 4) :=
  norm_tsum_ite_cpow_div_sub_tsum_ite_cpow_div_le (fun _ : Unit => (1 / 2 + 7 / 2 * I : ℂ))
    (fun _ => by norm_num) (by norm_num) (by norm_num) (Set.toFinite _)
    fun F _ => by exact_mod_cast Finset.card_le_univ F

/-- The sum over the odd trivial zeros `-(2m + 1)` at `x = 2`. -/
example : Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M,
    ((2 : ℝ) : ℂ) ^ (((1 : ℝ) : ℂ) - 2 * m) / (2 * m - ((1 : ℝ) : ℂ))) atTop
      (𝓝 (∑' m : ℕ, ((2 : ℝ) : ℂ) ^ (((1 : ℝ) : ℂ) - 2 * ((m : ℂ) + 1)) /
        (2 * ((m : ℂ) + 1) - ((1 : ℝ) : ℂ)))) :=
  tendsto_sum_cpow_sub_two_mul_div_two_mul_sub (by norm_num) le_rfl

end ExplicitFormulaContourTest
