/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Ancillary statistics

`IsAncillary P V`, for a family `P` of probability measures: the statistic `V` is
measurable and its pushforward law is the same probability measure for every parameter
value. Ancillary is not pivotal (no distributional shape is asserted), and ancillarity
does not imply independence of a sufficient statistic (that implication is Basu's theorem,
not proved here).

Source: G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Definition 6.2.24.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Sufficiency

open MeasureTheory

private theorem map_eq_dirac_of_ae_const {Ω τ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace τ] (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → τ) (c : τ)
    (h : ∀ᵐ ω ∂μ, V ω = c) : μ.map V = Measure.dirac c := by
  have hcongr : μ.map V = μ.map (fun _ => c) := Measure.map_congr h
  rw [hcongr, Measure.map_const, measure_univ, one_smul]

/-- A statistic `V : Ω → τ` is *ancillary* for the family of probability laws `P` if `V`
is measurable and its pushforward law is the same for every parameter value. Ancillary
is not pivotal (no distributional shape is asserted), and ancillarity does not imply
independence of a sufficient statistic (that implication is Basu's theorem).

Source: G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Definition 6.2.24. -/
def IsAncillary {Ω Θ τ : Type*} [MeasurableSpace Ω] [MeasurableSpace τ]
    (P : Θ → ProbabilityMeasure Ω) (V : Ω → τ) : Prop :=
  Measurable V ∧ ∀ θ₁ θ₂, ((P θ₁) : Measure Ω).map V = ((P θ₂) : Measure Ω).map V

/-- An almost-surely constant statistic is ancillary: every pushforward is the same Dirac
mass. -/
theorem isAncillary_of_ae_const {Ω Θ τ : Type*} [MeasurableSpace Ω] [MeasurableSpace τ]
    {P : Θ → ProbabilityMeasure Ω} {V : Ω → τ} {c : τ}
    (h : ∀ θ, ∀ᵐ ω ∂((P θ) : Measure Ω), V ω = c) (hm : Measurable V) :
    IsAncillary P V := by
  refine ⟨hm, fun θ₁ θ₂ => ?_⟩
  rw [map_eq_dirac_of_ae_const _ _ _ (h θ₁), map_eq_dirac_of_ae_const _ _ _ (h θ₂)]

/-- Ancillarity is preserved under measurable maps. -/
theorem IsAncillary.comp {Ω Θ τ σ : Type*} [MeasurableSpace Ω] [MeasurableSpace τ]
    [MeasurableSpace σ] {P : Θ → ProbabilityMeasure Ω} {V : Ω → τ} {W : τ → σ}
    (hV : IsAncillary P V) (hW : Measurable W) : IsAncillary P (W ∘ V) := by
  obtain ⟨hmV, heq⟩ := hV
  refine ⟨hW.comp hmV, fun θ₁ θ₂ => ?_⟩
  calc ((P θ₁) : Measure Ω).map (W ∘ V)
      = (((P θ₁) : Measure Ω).map V).map W := (Measure.map_map hW hmV).symm
    _ = (((P θ₂) : Measure Ω).map V).map W := by rw [heq θ₁ θ₂]
    _ = ((P θ₂) : Measure Ω).map (W ∘ V) := Measure.map_map hW hmV

end MathlibExt.Probability.Statistics.Sufficiency
