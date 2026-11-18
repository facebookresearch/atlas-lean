/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.Order.Field
public import MathlibExt.Biology.Biophysics.CompartmentKinetics

/-!
# Absorption limits

First-order absorption empties the gut (`D exp (-ka t) -> 0`),
and the central amount at distinct positive rates vanishes at
infinity.
-/

@[expose] public section

open Real Filter Topology

namespace MathlibExt.Biology.Biophysics.Absorption.Limit

set_option linter.unusedVariables false in
lemma exp_neg_mul_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t => Real.exp (-c * t)) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop hc)
  exact h.congr (fun t => by simp [Function.comp])

lemma gut_amount_tendsto {D ka : ℝ} (hka : 0 < ka) :
    Tendsto (fun t => D * Real.exp (-ka * t)) atTop (𝓝 0) := by
  have h := MathlibExt.Biology.Biophysics.CompartmentKinetics.tendsto_amount_bolus hka D
  have heq : (fun t => D * Real.exp (-ka * t)) =
      MathlibExt.Biology.Biophysics.CompartmentKinetics.amount ka 0 D := by
    funext t
    rw [MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_bolus]
  rwa [heq]

set_option linter.unusedVariables false in
/-- **Central amount vanishes at infinity.** The central amount at
distinct rates, `F * D * ka * (exp (-k t) - exp (-ka t)) / (ka - k)`
with `F ∈ [0,1]`, `D, ka, k ≥ 0`, tends to `0` as `t → ∞`, provided
both rates are positive. -/
lemma central_amount_tendsto {F D ka k : ℝ} (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (hD : 0 ≤ D) (hka : 0 < ka) (hk : 0 < k) (hne : ka ≠ k) :
    Tendsto (fun t => F * D * ka * (Real.exp (-k * t) - Real.exp (-ka * t)) / (ka - k))
      atTop (𝓝 0) := by
  have hk0 := exp_neg_mul_tendsto_zero hk
  have hka0 := exp_neg_mul_tendsto_zero hka
  have hdiff : Tendsto (fun t : ℝ => Real.exp (-k * t) - Real.exp (-ka * t)) atTop (𝓝 0) := by
    have h := hk0.sub hka0
    simpa using h
  have hmul : Tendsto (fun t : ℝ => F * D * ka * (Real.exp (-k * t) - Real.exp (-ka * t)))
      atTop (𝓝 0) := by
    have h := Filter.Tendsto.const_mul (F * D * ka) hdiff
    simpa using h
  have hdiv := Filter.Tendsto.div_const hmul (ka - k)
  simpa using hdiv

end MathlibExt.Biology.Biophysics.Absorption.Limit
