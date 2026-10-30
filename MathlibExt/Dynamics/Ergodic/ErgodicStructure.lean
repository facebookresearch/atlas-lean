/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Dynamics.Ergodic.KingmanSigned.BirkhoffPointwise

/-!
# Invariant σ-algebra, ergodicity and conditional expectation

Facts about the invariant σ-algebra `MeasurableSpace.invariants T` of a map `T`: functions with
`f ∘ T = f` are invariant-measurable and are their own conditional expectation, so their Birkhoff
averages converge to themselves; ergodicity is equivalent to measure preservation plus triviality
of the invariant σ-algebra; and for ergodic `T` invariant functions and the conditional expectation
on the invariant σ-algebra are a.e. equal to the mean.

The pre-ergodicity condition used here is the classical one with strictly invariant measurable
sets, `∀ s, MeasurableSet s → T ⁻¹' s = s → s is a.e. empty or full`. Mathlib's `PreErgodic`
(null-measurable, a.e.-invariant sets) is stronger when `T` is not quasi-measure-preserving, so
the theorems state the classical condition explicitly instead of naming `PreErgodic`.

## Main definitions

* `StatMech.ErgodicStructure.InvariantsTrivial`: every invariant set has measure `0` or `1`.

## Main results

* `StatMech.ErgodicStructure.ergodic_iff_invariantsTrivial`.
* `StatMech.ErgodicStructure.invariantsTrivial_iff_preErgodic`,
  `StatMech.ErgodicStructure.preErgodic_iff_forall_invariant_ae_const`: characterizations of the
  classical pre-ergodicity condition.
* `StatMech.ErgodicStructure.condExp_invariants_ae_eq_mean`: for ergodic `T`,
  `μ[f | invariants T] = ∫ f dμ` a.e.
-/

@[expose] public section

open MeasureTheory Filter Function MeasurableSpace
open scoped Topology ENNReal

namespace StatMech

namespace ErgodicStructure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {f : α → ℝ}

/-- A measurable `f` with `f ∘ T = f` is measurable for the invariant σ-algebra. -/
theorem measurable_invariants_of_comp_eq (hf : Measurable f) (hcomp : f ∘ T = f) :
    Measurable[MeasurableSpace.invariants T] f := by
  rw [MeasurableSpace.measurable_invariants_dom]
  refine ⟨hf, fun s _ => ?_⟩
  rw [hcomp]

/-- An invariant-measurable integrable function is its own conditional expectation on the invariant
σ-algebra. -/
theorem condExp_invariants_self [IsFiniteMeasure μ]
    (hf : StronglyMeasurable[MeasurableSpace.invariants T] f) (hfi : Integrable f μ) :
    μ[f | MeasurableSpace.invariants T] = f := by
  have hm : MeasurableSpace.invariants T ≤ ‹MeasurableSpace α› := MeasurableSpace.invariants_le T
  have hsf : SigmaFinite (μ.trim hm) := by
    have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
    infer_instance
  exact condExp_of_stronglyMeasurable hm hf hfi

/-- A measurable integrable `f` with `f ∘ T = f` is its own conditional expectation on the invariant
σ-algebra. -/
theorem condExp_of_comp_eq [IsFiniteMeasure μ]
    (hf : Measurable f) (hfi : Integrable f μ) (hcomp : f ∘ T = f) :
    μ[f | MeasurableSpace.invariants T] = f :=
  condExp_invariants_self (measurable_invariants_of_comp_eq hf hcomp).stronglyMeasurable hfi

/-- The Birkhoff averages of a measurable integrable `T`-invariant function converge a.e. to the
function itself. -/
theorem tendsto_birkhoffAverage_self_ae [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (hf : Measurable f) (hfi : Integrable f μ)
    (hcomp : f ∘ T = f) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (f x)) := by
  filter_upwards [StatMech.BirkhoffAE.tendsto_birkhoffAverage_condExp_ae hT hfi] with x hx
  rwa [condExp_of_comp_eq hf hfi hcomp] at hx

/-- The invariant σ-algebra of `T` is trivial for `μ`: every invariant set has measure `0` or
`1`. -/
def InvariantsTrivial (T : α → α) (μ : Measure α) : Prop :=
  ∀ s : Set α, MeasurableSet[MeasurableSpace.invariants T] s → μ s = 0 ∨ μ s = 1

/-- On a probability space, the invariant σ-algebra is trivial iff every strictly invariant
measurable set is a.e. empty or full (classical pre-ergodicity; not Mathlib's `PreErgodic`, see
the module docstring). -/
theorem invariantsTrivial_iff_preErgodic [IsProbabilityMeasure μ] :
    InvariantsTrivial T μ ↔
      ∀ ⦃s : Set α⦄, MeasurableSet s → T ⁻¹' s = s → EventuallyEmptyOrUniv s (ae μ) := by
  constructor
  · intro h s hs hs'
    rw [eventuallyEmptyOrUniv_iff']
    rcases h s ((MeasurableSpace.measurableSet_invariants).mpr ⟨hs, hs'⟩) with h0 | h1
    · left; simpa using h0
    · right
      rw [ae_eq_univ]
      have : μ sᶜ = 0 := by
        rw [measure_compl hs (measure_ne_top μ s), h1, measure_univ]; simp
      simpa using this
  · intro h s hs
    obtain ⟨hsm, hsinv⟩ := (MeasurableSpace.measurableSet_invariants).mp hs
    rcases eventuallyEmptyOrUniv_iff'.mp (h hsm hsinv) with h0 | h1
    · exact Or.inl (ae_eq_empty.mp h0)
    · exact Or.inr ((measure_congr h1).trans measure_univ)

/-- `T` is ergodic iff it is measure preserving and its invariant σ-algebra is trivial. -/
theorem ergodic_iff_invariantsTrivial [IsProbabilityMeasure μ] :
    Ergodic T μ ↔ MeasurePreserving T μ μ ∧ InvariantsTrivial T μ := by
  constructor
  · intro h
    refine ⟨h.toMeasurePreserving, fun s hs => ?_⟩
    obtain ⟨hsm, hsinv⟩ := (MeasurableSpace.measurableSet_invariants).mp hs
    exact h.prob_eq_zero_or_one hsm.nullMeasurableSet (by rw [hsinv])
  · rintro ⟨hmp, htriv⟩
    exact Ergodic.of_preimage_eq hmp (invariantsTrivial_iff_preErgodic.mp htriv)

/-- Classical pre-ergodicity holds iff every invariant-measurable real function is a.e. constant. -/
theorem preErgodic_iff_forall_invariant_ae_const [IsProbabilityMeasure μ] :
    (∀ ⦃s : Set α⦄, MeasurableSet s → T ⁻¹' s = s → EventuallyEmptyOrUniv s (ae μ)) ↔
      ∀ g : α → ℝ, Measurable[MeasurableSpace.invariants T] g → ∃ c, g =ᵐ[μ] fun _ => c := by
  constructor
  · intro h g hg
    have hgm : Measurable g := hg.mono (MeasurableSpace.invariants_le T) le_rfl
    have hg_eq : g ∘ T = g := MeasurableSpace.comp_eq_of_measurable_invariants hg
    exact exists_eventuallyEq_const_of_forall_separating MeasurableSet fun U hU ↦
      eventuallyEmptyOrUniv_iff.1 <| h (s := g ⁻¹' U) (hgm hU) <| by rw [← Set.preimage_comp, hg_eq]
  · intro h s hs hs'
    have hsinv : MeasurableSet[MeasurableSpace.invariants T] s :=
      (MeasurableSpace.measurableSet_invariants).mpr ⟨hs, hs'⟩
    have hind : Measurable[MeasurableSpace.invariants T] (s.indicator (fun _ => (1 : ℝ))) :=
      measurable_const.indicator hsinv
    obtain ⟨c, hc⟩ := h _ hind
    rw [eventuallyEmptyOrUniv_iff]
    by_cases hc1 : c = 1
    · left
      filter_upwards [hc] with x hx
      by_contra hxs
      rw [Set.indicator_of_notMem hxs, hc1] at hx; norm_num at hx
    · right
      filter_upwards [hc] with x hx
      intro hxs
      rw [Set.indicator_of_mem hxs] at hx; exact hc1 hx.symm

/-- For ergodic `T`, an integrable invariant-measurable function is a.e. equal to its mean. -/
theorem ae_eq_mean_of_invariants [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hf : Integrable f μ)
    (hfm : StronglyMeasurable[MeasurableSpace.invariants T] f) :
    f =ᵐ[μ] fun _ => ∫ x, f x ∂μ := by
  have hcomp : f ∘ T = f := MeasurableSpace.comp_eq_of_measurable_invariants hfm.measurable
  obtain ⟨c, hc⟩ := hT.ae_eq_const_of_ae_eq_comp_ae hf.aestronglyMeasurable (by rw [hcomp])
  have hint : ∫ x, f x ∂μ = c := by rw [integral_congr_ae hc]; simp
  rw [hint]; exact hc

/-- For ergodic `T`, the conditional expectation on the invariant σ-algebra is a.e. the mean
`∫ f dμ`. The integrability hypothesis is not used. -/
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

end ErgodicStructure

end StatMech
