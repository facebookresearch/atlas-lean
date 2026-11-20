/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































import Mathlib
import Code.Foundations.BirkhoffPointwise

open MeasureTheory Filter Function MeasurableSpace
open scoped Topology ENNReal

namespace StatMech

namespace ErgodicStructure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {f : α → ℝ}





theorem measurable_invariants_of_comp_eq (hf : Measurable f) (hcomp : f ∘ T = f) :
    Measurable[MeasurableSpace.invariants T] f := by
  rw [MeasurableSpace.measurable_invariants_dom]
  refine ⟨hf, fun s _ => ?_⟩
  rw [hcomp]



theorem condExp_invariants_self [IsFiniteMeasure μ]
    (hf : StronglyMeasurable[MeasurableSpace.invariants T] f) (hfi : Integrable f μ) :
    μ[f | MeasurableSpace.invariants T] = f := by
  have hm : MeasurableSpace.invariants T ≤ ‹MeasurableSpace α› := MeasurableSpace.invariants_le T
  have hsf : SigmaFinite (μ.trim hm) := by
    have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
    infer_instance
  exact condExp_of_stronglyMeasurable hm hf hfi



theorem condExp_of_comp_eq [IsFiniteMeasure μ]
    (hf : Measurable f) (hfi : Integrable f μ) (hcomp : f ∘ T = f) :
    μ[f | MeasurableSpace.invariants T] = f :=
  condExp_invariants_self (measurable_invariants_of_comp_eq hf hcomp).stronglyMeasurable hfi





theorem tendsto_birkhoffAverage_self_ae [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (hf : Measurable f) (hfi : Integrable f μ)
    (hcomp : f ∘ T = f) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (f x)) := by
  filter_upwards [StatMech.BirkhoffAE.tendsto_birkhoffAverage_condExp_ae hT hfi] with x hx
  rwa [condExp_of_comp_eq hf hfi hcomp] at hx





def InvariantsTrivial (T : α → α) (μ : Measure α) : Prop :=
  ∀ s : Set α, MeasurableSet[MeasurableSpace.invariants T] s → μ s = 0 ∨ μ s = 1




theorem invariantsTrivial_iff_preErgodic [IsProbabilityMeasure μ] :
    InvariantsTrivial T μ ↔ PreErgodic T μ := by
  constructor
  · intro h
    refine ⟨fun s hs hs' => ?_⟩
    rw [eventuallyConst_set']
    rcases h s ((MeasurableSpace.measurableSet_invariants).mpr ⟨hs, hs'⟩) with h0 | h1
    · left; simpa using h0
    · right
      rw [ae_eq_univ]
      have : μ sᶜ = 0 := by
        rw [measure_compl hs (measure_ne_top μ s), h1, measure_univ]; simp
      simpa using this
  · intro h s hs
    obtain ⟨hsm, hsinv⟩ := (MeasurableSpace.measurableSet_invariants).mp hs
    exact h.prob_eq_zero_or_one hsm hsinv



theorem ergodic_iff_invariantsTrivial [IsProbabilityMeasure μ] :
    Ergodic T μ ↔ MeasurePreserving T μ μ ∧ InvariantsTrivial T μ := by
  constructor
  · intro h
    exact ⟨h.toMeasurePreserving, invariantsTrivial_iff_preErgodic.mpr h.toPreErgodic⟩
  · rintro ⟨hmp, htriv⟩
    exact ⟨hmp, invariantsTrivial_iff_preErgodic.mp htriv⟩









theorem preErgodic_iff_forall_invariant_ae_const [IsProbabilityMeasure μ] :
    PreErgodic T μ ↔
      ∀ g : α → ℝ, Measurable[MeasurableSpace.invariants T] g → ∃ c, g =ᵐ[μ] fun _ => c := by
  constructor
  · intro h g hg
    have hgm : Measurable g := hg.mono (MeasurableSpace.invariants_le T) le_rfl
    exact h.ae_eq_const_of_ae_eq_comp hgm
      (MeasurableSpace.comp_eq_of_measurable_invariants hg)
  · intro h
    refine ⟨fun s hs hs' => ?_⟩
    have hsinv : MeasurableSet[MeasurableSpace.invariants T] s :=
      (MeasurableSpace.measurableSet_invariants).mpr ⟨hs, hs'⟩
    have hind : Measurable[MeasurableSpace.invariants T] (s.indicator (fun _ => (1 : ℝ))) :=
      measurable_const.indicator hsinv
    obtain ⟨c, hc⟩ := h _ hind
    rw [eventuallyConst_set]
    by_cases hc1 : c = 1
    · left
      filter_upwards [hc] with x hx
      by_contra hxs
      rw [Set.indicator_of_notMem hxs, hc1] at hx; norm_num at hx
    · right
      filter_upwards [hc] with x hx
      intro hxs
      rw [Set.indicator_of_mem hxs] at hx; exact hc1 hx.symm






theorem ae_eq_mean_of_invariants [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hf : Integrable f μ)
    (hfm : StronglyMeasurable[MeasurableSpace.invariants T] f) :
    f =ᵐ[μ] fun _ => ∫ x, f x ∂μ := by
  have hcomp : f ∘ T = f := MeasurableSpace.comp_eq_of_measurable_invariants hfm.measurable
  obtain ⟨c, hc⟩ := hT.ae_eq_const_of_ae_eq_comp_ae hf.aestronglyMeasurable (by rw [hcomp])
  have hint : ∫ x, f x ∂μ = c := by rw [integral_congr_ae hc]; simp
  rw [hint]; exact hc




theorem condExp_invariants_ae_eq_mean [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (_hf : Integrable f μ) :
    μ[f | MeasurableSpace.invariants T] =ᵐ[μ] fun _ => ∫ x, f x ∂μ := by
  have hm : MeasurableSpace.invariants T ≤ ‹MeasurableSpace α› := MeasurableSpace.invariants_le T
  have hge : StronglyMeasurable[MeasurableSpace.invariants T]
      (μ[f | MeasurableSpace.invariants T]) := stronglyMeasurable_condExp
  have hcomp : (μ[f | MeasurableSpace.invariants T]) ∘ T = μ[f | MeasurableSpace.invariants T] :=
    MeasurableSpace.comp_eq_of_measurable_invariants hge.measurable
  obtain ⟨c, hc⟩ := hT.ae_eq_const_of_ae_eq_comp_ae integrable_condExp.aestronglyMeasurable
    (by rw [hcomp])
  have hsf : SigmaFinite (μ.trim hm) := by
    have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
    infer_instance
  have hintc : ∫ x, (μ[f | MeasurableSpace.invariants T]) x ∂μ = c := by
    rw [integral_congr_ae hc]; simp
  rw [integral_condExp hm] at hintc
  rw [hintc]; exact hc




theorem tendsto_birkhoffAverage_mean_ae [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (∫ y, f y ∂μ)) := by
  filter_upwards [StatMech.BirkhoffAE.tendsto_birkhoffAverage_condExp_ae hT.toMeasurePreserving hf,
    condExp_invariants_ae_eq_mean hT hf] with x hx hxeq
  rwa [hxeq] at hx

end ErgodicStructure

end StatMech
