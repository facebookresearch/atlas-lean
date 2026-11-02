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

/-- The `θ`-independent second-coin density factor: the second coin is always fair. -/
def secondCoinDensity : (Bool × Bool) → ℝ≥0∞ := fun _ => 1 / 2

/-- The first-coin density factor: the first coin lands on `θ` with probability `3 / 4`. -/
def firstCoinDensity (θ : Bool) (t : Bool) : ℝ≥0∞ := if t = θ then 3 / 4 else 1 / 4

/-- The two-coin family: first coin biased towards `θ`, second coin fair, as a density
with respect to counting measure. -/
noncomputable def twoCoinFamily (θ : Bool) : Measure (Bool × Bool) :=
  Measure.count.withDensity fun ω => firstCoinDensity θ (Prod.fst ω) * secondCoinDensity ω

theorem measurable_firstCoinDensity (θ : Bool) : Measurable (firstCoinDensity θ) := by
  intro _ _
  trivial

theorem measurable_secondCoinDensity : Measurable secondCoinDensity := by
  intro _ _
  trivial

instance (θ : Bool) : IsFiniteMeasure (twoCoinFamily θ) := by
  refine ⟨?_⟩
  rw [twoCoinFamily, Measure.withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    lintegral_count, tsum_fintype, ENNReal.lt_top_iff_ne_top]
  apply Finset.sum_ne_top
  intro ω _
  by_cases h : Prod.fst ω = θ <;> simp [h, firstCoinDensity, secondCoinDensity]

instance : IsFiniteMeasure (Measure.count.withDensity secondCoinDensity) := by
  refine ⟨?_⟩
  rw [Measure.withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, lintegral_count,
    tsum_fintype, ENNReal.lt_top_iff_ne_top]
  apply Finset.sum_ne_top
  intro _ _
  simp [secondCoinDensity]

/-- The first coin is sufficient for the two-coin family, via the σ-algebra form of the
factorization criterion: the density factors through `Prod.fst` against the fair
second-coin base measure. -/
example : IsSufficient (MeasurableSpace.comap Prod.fst inferInstance) twoCoinFamily := by
  refine isSufficient_of_withDensity le_top (Measure.count.withDensity secondCoinDensity)
    (fun θ ω => firstCoinDensity θ (Prod.fst ω)) ?_ ?_
  · intro θ
    exact (measurable_firstCoinDensity θ).comp (comap_measurable Prod.fst)
  · intro θ
    rw [twoCoinFamily, withDensity_mul Measure.count measurable_secondCoinDensity
      ((measurable_firstCoinDensity θ).comp measurable_fst)]
    congr 1
    ext ω
    rw [Pi.mul_apply, mul_comm]

/-- The first coin is sufficient for the two-coin family, via the statistic form of the
factorization criterion: the density is `g θ (Prod.fst ω) * h ω` with `h` independent
of `θ`. -/
example : IsSufficient (MeasurableSpace.comap Prod.fst inferInstance) twoCoinFamily := by
  refine isSufficient_comap_of_factorization_of_sigmaFinite_trim measurable_fst Measure.count
    firstCoinDensity (fun θ => measurable_firstCoinDensity θ) secondCoinDensity
    measurable_secondCoinDensity ?_
  intro θ
  rfl

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
