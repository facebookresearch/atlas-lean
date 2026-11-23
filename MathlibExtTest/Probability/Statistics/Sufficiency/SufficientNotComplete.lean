/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sufficiency.Complete
public import MathlibExt.Probability.Statistics.Sufficiency.Basic

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Sufficiency.SufficientNotComplete



open MeasureTheory



-- Private helpers for the witness `X₁ − X₂` below.



private theorem witness_measurable :

    Measurable (fun ω : Bool × Bool => (if ω.1 then (1 : ℝ) else 0) - (if ω.2 then 1 else 0)) :=

  Measurable.of_discrete



private theorem witness_integrable {P : Set.Ioo (0 : ℝ) 1 → ProbabilityMeasure (Bool × Bool)}

    (p : Set.Ioo (0 : ℝ) 1) :

    Integrable (fun ω : Bool × Bool => (if ω.1 then (1 : ℝ) else 0) - (if ω.2 then 1 else 0))

      ((P p) : Measure (Bool × Bool)) := by

  refine Integrable.of_bound witness_measurable.aestronglyMeasurable 1 ?_

  filter_upwards with ω

  obtain ⟨b₁, b₂⟩ := ω

  cases b₁ <;> cases b₂ <;> norm_num



private theorem witness_zero_mean {P : Set.Ioo (0 : ℝ) 1 → ProbabilityMeasure (Bool × Bool)}

    (hmass : ∀ p, ∀ b₁ b₂ : Bool, ((P p) : Measure (Bool × Bool)) {(b₁, b₂)} =

      ENNReal.ofReal ((if b₁ then p.val else 1 - p.val) *

        (if b₂ then p.val else 1 - p.val))) (p : Set.Ioo (0 : ℝ) 1) :

    ∫ ω : Bool × Bool, ((if ω.1 then (1 : ℝ) else 0) - (if ω.2 then 1 else 0)) ∂

      ((P p) : Measure (Bool × Bool)) = 0 := by

  have hp0 : 0 ≤ p.val := le_of_lt p.2.1

  have hp1 : 0 ≤ 1 - p.val := sub_nonneg.2 (le_of_lt p.2.2)

  have hreal : ∀ b₁ b₂ : Bool, ((P p) : Measure (Bool × Bool)).real {(b₁, b₂)} =

      (if b₁ then p.val else 1 - p.val) * (if b₂ then p.val else 1 - p.val) := by

    intro b₁ b₂

    rw [Measure.real_def, hmass]

    apply ENNReal.toReal_ofReal

    cases b₁ <;> cases b₂ <;> simp <;> positivity

  rw [integral_fintype (witness_integrable p), Fintype.sum_prod_type]

  simp only [Fintype.sum_bool, hreal, smul_eq_mul]

  simp

  ring



private theorem witness_not_ae_zero {P : Set.Ioo (0 : ℝ) 1 → ProbabilityMeasure (Bool × Bool)}

    (hmass : ∀ p, ∀ b₁ b₂ : Bool, ((P p) : Measure (Bool × Bool)) {(b₁, b₂)} =

      ENNReal.ofReal ((if b₁ then p.val else 1 - p.val) *

        (if b₂ then p.val else 1 - p.val))) (p : Set.Ioo (0 : ℝ) 1) :

    ¬ (fun ω : Bool × Bool => (if ω.1 then (1 : ℝ) else 0) - (if ω.2 then 1 else 0)) =ᵐ[

      ((P p) : Measure (Bool × Bool))] 0 := by

  intro h

  have hmeas : MeasurableSet

      {ω : Bool × Bool | (if ω.1 then (1 : ℝ) else 0) - (if ω.2 then 1 else 0) = 0} :=

    witness_measurable (measurableSet_singleton 0)

  have hfull : ((P p) : Measure (Bool × Bool))

      {ω : Bool × Bool | (if ω.1 then (1 : ℝ) else 0) - (if ω.2 then 1 else 0) = 0} =

      ((P p) : Measure (Bool × Bool)) Set.univ :=

    (ae_iff_measure_eq hmeas.nullMeasurableSet).mp h

  have hcompl : ((P p) : Measure (Bool × Bool))

      {ω : Bool × Bool | (if ω.1 then (1 : ℝ) else 0) - (if ω.2 then 1 else 0) = 0}ᶜ = 0 := by

    rw [measure_compl hmeas (measure_ne_top _ _), hfull]

    simp

  have hsub : ({(true, false)} : Set (Bool × Bool)) ⊆

      {ω : Bool × Bool | (if ω.1 then (1 : ℝ) else 0) - (if ω.2 then 1 else 0) = 0}ᶜ := by

    intro ω hω

    simp only [Set.mem_singleton_iff] at hω

    subst hω

    simp

  have hle : ((P p) : Measure (Bool × Bool)) {(true, false)} ≤

      ((P p) : Measure (Bool × Bool))

        {ω : Bool × Bool | (if ω.1 then (1 : ℝ) else 0) - (if ω.2 then 1 else 0) = 0}ᶜ :=

    measure_mono hsub

  rw [hcompl] at hle

  have hzero : ((P p) : Measure (Bool × Bool)) {(true, false)} = 0 := bot_unique hle

  have hpos : ((P p) : Measure (Bool × Bool)) {(true, false)} ≠ 0 := by

    rw [hmass]

    simp

    exact mul_pos p.2.1 (sub_pos.2 p.2.2)

  exact hpos hzero



private theorem witness_not_complete {P : Set.Ioo (0 : ℝ) 1 → ProbabilityMeasure (Bool × Bool)}

    (hmass : ∀ p, ∀ b₁ b₂ : Bool, ((P p) : Measure (Bool × Bool)) {(b₁, b₂)} =

      ENNReal.ofReal ((if b₁ then p.val else 1 - p.val) *

        (if b₂ then p.val else 1 - p.val))) :

    ¬ MathlibExt.Probability.Statistics.Sufficiency.IsCompleteStatistic P id := by

  intro hC

  obtain ⟨-, hcomp⟩ := hC

  have hae := hcomp (fun ω : Bool × Bool => (if ω.1 then (1 : ℝ) else 0) - (if ω.2 then 1 else 0))

    witness_measurable (fun θ => witness_integrable θ) (fun θ => witness_zero_mean hmass θ)

  obtain ⟨p, hp⟩ := Set.nonempty_Ioo.2 (show (0 : ℝ) < 1 by norm_num)

  exact witness_not_ae_zero hmass ⟨p, hp⟩ (hae ⟨p, hp⟩)



-- PINNED EXAMPLES (prove each sorry; no production declarations)



/-- The identity statistic is sufficient for every finite family on a discrete space —

the sufficiency half of the advertised boundary, proved from discreteness. -/

example {P : Set.Ioo (0 : ℝ) 1 → Measure (Bool × Bool)}

    [∀ p, IsProbabilityMeasure (P p)] :

    MathlibExt.Probability.Statistics.Sufficiency.IsSufficient

      (MeasurableSpace.comap (id : Bool × Bool → Bool × Bool) inferInstance) P := by

  refine ⟨measurable_id.comap_le, fun θ => inferInstance, fun s hs => ?_⟩

  have h0 : StronglyMeasurable (s.indicator (fun _ => (1 : ℝ))) :=

    (measurable_const.indicator hs).stronglyMeasurable

  have h1 : StronglyMeasurable[MeasurableSpace.comap id inferInstance]

      (s.indicator (fun _ => (1 : ℝ))) := by

    have h := h0.comp_measurable (comap_measurable (id : Bool × Bool → Bool × Bool))

    rwa [Function.comp_id] at h

  refine ⟨s.indicator (fun _ => (1 : ℝ)), h1, fun θ => ?_⟩

  have hfi : Integrable (s.indicator (fun _ => (1 : ℝ))) (P θ) :=

    (integrable_const 1).indicator hs

  exact (condExp_of_aestronglyMeasurable' measurable_id.comap_le h1.aestronglyMeasurable

    hfi).symm



/-- The `X₁ − X₂` witness has mean zero under every interior Bernoulli-pair law. -/

example {P : Set.Ioo (0 : ℝ) 1 → ProbabilityMeasure (Bool × Bool)}

    (hmass : ∀ p, ∀ b₁ b₂ : Bool, ((P p) : Measure (Bool × Bool)) {(b₁, b₂)} =

      ENNReal.ofReal ((if b₁ then p.val else 1 - p.val) *

        (if b₂ then p.val else 1 - p.val))) (p : Set.Ioo (0 : ℝ) 1) :

    ∫ ω : Bool × Bool, ((if ω.1 then (1 : ℝ) else 0) - (if ω.2 then 1 else 0)) ∂

      ((P p) : Measure (Bool × Bool)) = 0 := by

  exact witness_zero_mean hmass p



/-- The witness is not almost-everywhere zero: it equals one at `(true, false)`, which

carries positive mass `p(1-p)` for interior `p`. -/

example {P : Set.Ioo (0 : ℝ) 1 → ProbabilityMeasure (Bool × Bool)}

    (hmass : ∀ p, ∀ b₁ b₂ : Bool, ((P p) : Measure (Bool × Bool)) {(b₁, b₂)} =

      ENNReal.ofReal ((if b₁ then p.val else 1 - p.val) *

        (if b₂ then p.val else 1 - p.val))) (p : Set.Ioo (0 : ℝ) 1) :

    ¬ (fun ω : Bool × Bool => (if ω.1 then (1 : ℝ) else 0) - (if ω.2 then 1 else 0)) =ᵐ[

      ((P p) : Measure (Bool × Bool))] 0 := by

  exact witness_not_ae_zero hmass p



/-- **Sufficient need not be complete.** The Bernoulli pair with the full-sample statistic

admits a nonzero-mean-zero witness, so it is not complete. -/

example {P : Set.Ioo (0 : ℝ) 1 → ProbabilityMeasure (Bool × Bool)}

    (hmass : ∀ p, ∀ b₁ b₂ : Bool, ((P p) : Measure (Bool × Bool)) {(b₁, b₂)} =

      ENNReal.ofReal ((if b₁ then p.val else 1 - p.val) *

        (if b₂ then p.val else 1 - p.val))) :

    ¬ MathlibExt.Probability.Statistics.Sufficiency.IsCompleteStatistic P id := by

  exact witness_not_complete hmass



end MathlibExtTest.Probability.Statistics.Sufficiency.SufficientNotComplete
