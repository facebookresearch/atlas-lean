/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# A lower bound for the Gamma function

Splitting Euler's integral at `x` gives a positive integral on `(0, x)` and a tail on
which `t ^ x ≥ x ^ x`.
-/

namespace MetaMathlibExt

open MeasureTheory Real Set

/-- **Lower bound $\Gamma(x + 1) > (x/e)^x$ for the Gamma function.** For every real number
$x \ge 1$, $\Gamma(x + 1) > (x/e)^x$.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of
Integer Sequences 28 (2025), Article 25.2.8, Lemma 9 (`jis-2025-25.2.8-lem-9`). -/
public theorem div_exp_one_rpow_lt_Gamma_add_one {x : ℝ} (hx : 1 ≤ x) :
    (x / Real.exp 1) ^ x < Real.Gamma (x + 1) := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hx₁ : 0 < x + 1 := by positivity
  let f (t : ℝ) := exp (-t) * t ^ x
  have hf : IntegrableOn f (Ioi 0) := by
    simpa only [f, add_sub_cancel_right] using GammaIntegral_convergent hx₁
  have htail := hf.mono_set (Ioi_subset_Ioi hx₀.le)
  have hpos : 0 < ∫ t in 0..x, f t := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hx₀
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx₀.le).2
        (hf.mono_set Ioc_subset_Ioi_self)
    · exact fun t ht => mul_pos (exp_pos _) (rpow_pos_of_pos ht.1 _)
  calc
    (x / exp 1) ^ x = exp (-x) * x ^ x := by
      rw [div_rpow hx₀.le (exp_pos _).le, ← exp_mul, one_mul, exp_neg, div_eq_inv_mul]
    _ = ∫ t in Ioi x, exp (-t) * x ^ x := by rw [integral_mul_const, integral_exp_neg_Ioi]
    _ ≤ ∫ t in Ioi x, f t := by
      apply setIntegral_mono_on ((integrableOn_exp_neg_Ioi x).mul_const _) htail measurableSet_Ioi
      exact fun t ht => mul_le_mul_of_nonneg_left (rpow_le_rpow hx₀.le ht.le hx₀.le) (exp_pos _).le
    _ < (∫ t in 0..x, f t) + ∫ t in Ioi x, f t := lt_add_of_pos_left _ hpos
    _ = Gamma (x + 1) := by
      rw [intervalIntegral.integral_interval_add_Ioi hf htail, Gamma_eq_integral hx₁,
        add_sub_cancel_right]

end MetaMathlibExt
