/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The sample law of an i.i.d. tuple

If random variables `X i`, `i : Fin n`, are mutually independent and each has law `ν`, the
tuple `ω ↦ (X i ω)ᵢ` has law `νⁿ = Measure.pi (fun _ => ν)`, and conversely. Consequently the
sampling distribution of a measurable statistic `T` of the sample is `(νⁿ).map T`. The forward
direction is Mathlib's `ProbabilityTheory.iIndepFun.hasLaw_pi`; the results here hold for every
`n`, including `n = 0`.

## Main results

* `iIndepFun_and_hasLaw_of_hasLaw_tuple_pi`: a tuple with law `νⁿ` has independent coordinates,
  each with law `ν`.
* `hasLaw_statistic`: the sampling distribution of a measurable statistic.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Statistics

/-- **Converse of `iIndepFun.hasLaw_pi`.** If the tuple has law `νⁿ`, the coordinates are
independent and each has law `ν`. -/
theorem iIndepFun_and_hasLaw_of_hasLaw_tuple_pi {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure S}
    [IsProbabilityMeasure ν] {n : ℕ} {X : Fin n → Ω → S}
    (h : HasLaw (fun ω i => X i ω) (Measure.pi fun _ : Fin n => ν) μ) :
    iIndepFun X μ ∧ ∀ i, HasLaw (X i) ν μ := by
  have hX : ∀ i, HasLaw (X i) ν μ := fun i =>
    (measurePreserving_eval (fun _ : Fin n => ν) i).hasLaw.comp h
  exact ⟨(iIndepFun_iff_hasLaw_pi_pi hX).2 h, hX⟩

/-- **Sampling distribution of a statistic.** For a measurable statistic `T` of an i.i.d.
tuple with marginal law `ν`, `T (X₁, …, Xₙ)` has law `(νⁿ).map T`. -/
theorem hasLaw_statistic {Ω S U : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [MeasurableSpace U] {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure S}
    [IsProbabilityMeasure ν] {n : ℕ} {X : Fin n → Ω → S} (hlaw : ∀ i, HasLaw (X i) ν μ)
    (hind : iIndepFun X μ) {T : (Fin n → S) → U} (hT : Measurable T) :
    HasLaw (fun ω => T fun i => X i ω) ((Measure.pi fun _ : Fin n => ν).map T) μ := by
  exact (hasLaw_map hT.aemeasurable).comp (hind.hasLaw_pi hlaw)

end MathlibExt.Probability.Statistics
