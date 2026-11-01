/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sufficiency.Basic

@[expose] public section

open MeasureTheory MathlibExt.Probability.Statistics.Sufficiency

namespace MathlibExtTest.Probability.Statistics.Sufficiency.Basic

/-- Non-vacuity: the full σ-algebra is sufficient for every family of probability measures
(the indicator itself is a common version). -/
example {Ω Θ : Type*} [m₀ : MeasurableSpace Ω] (P : Θ → Measure Ω)
    [∀ θ, IsProbabilityMeasure (P θ)] : IsSufficient m₀ P := by
  refine ⟨le_rfl, fun θ => inferInstance, fun s hs => ?_⟩
  have hsm : StronglyMeasurable[m₀] (s.indicator fun _ => (1 : ℝ)) :=
    (stronglyMeasurable_const.indicator hs)
  refine ⟨s.indicator fun _ => (1 : ℝ), hsm, fun θ => ?_⟩
  rw [condExp_of_stronglyMeasurable le_rfl hsm ((integrable_const 1).indicator hs)]

/-- A family with one finite law: every sub-σ-algebra of `m₀` is sufficient. -/
example {Ω Θ : Type*} {m m₀ : MeasurableSpace Ω} (hm : m ≤ m₀) (μ : Measure[m₀] Ω)
    [IsFiniteMeasure μ] :
    IsSufficient m (fun _ : Θ => μ) := ⟨hm, fun _ => inferInstance, fun s _ =>
  ⟨μ[s.indicator fun _ => (1 : ℝ) | m], stronglyMeasurable_condExp, fun _ => .rfl⟩⟩

/-- The two point masses on `Bool`. -/
noncomputable def diracs (b : Bool) : Measure Bool := Measure.dirac b

instance (b : Bool) : IsProbabilityMeasure (diracs b) := by
  unfold diracs
  infer_instance

/-- The trivial σ-algebra is not sufficient for `{δ_true, δ_false}`: a common version of
`P_b(true | ⊥)` would be a constant equal to both `1` and `0`. -/
theorem not_isSufficient_bot : ¬ IsSufficient ⊥ diracs := by
  intro h
  obtain ⟨f, hf, hfθ⟩ := h.2.2 {true} (measurableSet_singleton true)
  obtain ⟨c, hc⟩ := stronglyMeasurable_bot_iff.mp hf
  subst hc
  have h1 := hfθ true
  have h0 := hfθ false
  simp only [condExp_bot, diracs, Filter.EventuallyEq, ae_dirac_eq, Filter.eventually_pure,
    integral_dirac] at h1 h0
  simp at h1 h0
  linarith

end MathlibExtTest.Probability.Statistics.Sufficiency.Basic
