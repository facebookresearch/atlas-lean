/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Two-exponential decay expansion

Difference-of-exponentials components at distinct nonnegative
rates, and the equal-rate limit form `A t exp (-ka t)`, are
nonnegative on `t >= 0` for nonnegative amplitude: the slower
exponential dominates.
-/

@[expose] public section

open Real

namespace MathlibExt.Biology.Biophysics.CompartmentKinetics.DecayExpansion

set_option linter.unusedVariables false in
/-- **Eigen-decay expansion at distinct rates.** At distinct rates
`ka ≠ ke`, any solution component of the form
`A (exp (-ke * t) - exp (-ka * t)) / (ka - ke)` is nonnegative on
`t ≥ 0` whenever `A ≥ 0` and `ka, ke ≥ 0`: the slower exponential
dominates the faster one. -/
lemma decay_expansion_nonneg {A ka ke t : ℝ} (hA : 0 ≤ A)
    (hka : 0 ≤ ka) (hke : 0 ≤ ke) (ht : 0 ≤ t) (hne : ka ≠ ke) :
    0 ≤ A * (Real.exp (-ke * t) - Real.exp (-ka * t)) / (ka - ke) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hkt : ka * t ≤ ke * t := mul_le_mul_of_nonneg_right (le_of_lt h) ht
    have hneg : -ke * t ≤ -ka * t := by
      simpa only [neg_mul] using neg_le_neg hkt
    have hexp : Real.exp (-ke * t) ≤ Real.exp (-ka * t) :=
      Real.exp_le_exp_of_le hneg
    have hnum : Real.exp (-ke * t) - Real.exp (-ka * t) ≤ 0 :=
      sub_nonpos.mpr hexp
    have hAnum : A * (Real.exp (-ke * t) - Real.exp (-ka * t)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hA hnum
    have hden : ka - ke ≤ 0 := sub_nonpos.mpr (le_of_lt h)
    exact div_nonneg_of_nonpos hAnum hden
  · have hkt : ke * t ≤ ka * t := mul_le_mul_of_nonneg_right (le_of_lt h) ht
    have hneg : -ka * t ≤ -ke * t := by
      simpa only [neg_mul] using neg_le_neg hkt
    have hexp : Real.exp (-ka * t) ≤ Real.exp (-ke * t) :=
      Real.exp_le_exp_of_le hneg
    have hnum : 0 ≤ Real.exp (-ke * t) - Real.exp (-ka * t) :=
      sub_nonneg.mpr hexp
    have hAnum : 0 ≤ A * (Real.exp (-ke * t) - Real.exp (-ka * t)) :=
      mul_nonneg hA hnum
    have hden : 0 ≤ ka - ke := sub_nonneg.mpr (le_of_lt h)
    exact div_nonneg hAnum hden

/-- **Equal-rate limit form.** For `A ≥ 0` and `ka ≥ 0`, at equal rates the component is
`A * t * exp (-ka * t) ≥ 0` on `t ≥ 0`. -/
lemma decay_equal_rate_nonneg {A ka t : ℝ} (hA : 0 ≤ A)
    (hka : 0 ≤ ka) (ht : 0 ≤ t) :
    0 ≤ A * t * Real.exp (-ka * t) := by
  exact mul_nonneg (mul_nonneg hA ht) (Real.exp_nonneg _)

end MathlibExt.Biology.Biophysics.CompartmentKinetics.DecayExpansion
