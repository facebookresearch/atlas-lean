/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.OptionalStopping

/-!
# Measure preservation of the tail selection via partitions

A map that agrees on each piece of a measurable partition with a measure-preserving map, with
matching restricted sums, is measure preserving; this reduces the tail selection to restricted sums.

## i. Overview

`tsm_measurePreserving_of_partition` is the gluing lemma, conditional on the restricted-sum
identities. `tsm_switchPiece` is the piece on which the stopping value equals `s`.
`tsm_TailSelMP_restrictedSum` packages the restricted-sum identity; it holds for a head-determined
stopping value (`tsm_restrictedSum_of_const`). The tail-selection files (`TailSelMP`,
`TailSelMPRecovery`, `TailSelMPSplice`, `OptionalStopping`) prove that the stopped tail selection is
measure preserving, which `TailCondLawConstant` turns into the tail conditional law. This file is
one step of the OSSS chain for monotonic measures: `AdaptMConditional` (OSSS from
`AdaptStepCovBound`) ← `AdaptDisintegration` (`AdaptCondBBB` ⇒ `AdaptStepCovBound`) ←
`AdaptCondReduction` (`acp_TailCondLaw` ⇒ `AdaptCondBBB`) ← `TailCondLawConstant` / `CrossMonotone`
(`acp_TailCondLaw` for monotonic measures), assembled unconditionally in
`MonotoneOSSSAssembly.osss_monotone_sharp`.

## ii. Key results

- `tsm_tailSelMP_of_restrictedSum`: restricted sums ⇒ measure-preserving tail selection.

## iii. Table of contents

- A. Gluing along partitions
- B. Restricted sums

## iv. References

* R. O'Donnell, M. Saks, O. Schramm, R. Servedio, *Every decision tree has an influential variable*,
  FOCS 2005.
-/

@[expose] public section

open scoped BigOperators ENNReal
open Finset MeasureTheory


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly
open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]

lemma tsm_map_restrict_congr {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (S : Set α) {h h' : α → β} (hh : Measurable h) (hh' : Measurable h')
    (hagree : ∀ x ∈ S, h x = h' x) :
    Measure.map h (μ.restrict S) = Measure.map h' (μ.restrict S) := by
  ext T hT
  rw [Measure.map_apply hh hT, Measure.map_apply hh' hT,
      Measure.restrict_apply (hh hT), Measure.restrict_apply (hh' hT)]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  constructor <;> rintro ⟨hx, hxs⟩ <;> refine ⟨?_, hxs⟩
  · rwa [← hagree x hxs]
  · rwa [hagree x hxs]

/-! ## A. Gluing along partitions -/

lemma tsm_measurePreserving_of_partition {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} {S : ℕ → Set α}
    (hSmeas : ∀ k, MeasurableSet (S k)) (hSdisj : Pairwise (Function.onFun Disjoint S))
    (hScover : ⋃ k, S k = Set.univ) {h : α → β} (hh : Measurable h) {hk : ℕ → α → β}
    (hhk : ∀ k, Measurable (hk k)) (hagree : ∀ k, ∀ x ∈ S k, h x = hk k x)
    (hsum : (Measure.sum (fun k => Measure.map (hk k) (μ.restrict (S k)))) = ν) :
    MeasurePreserving h μ ν := by
  refine ⟨hh, ?_⟩
  have hμsum : μ = Measure.sum (fun k => μ.restrict (S k)) := by
    conv_lhs => rw [← Measure.restrict_univ (μ := μ), ← hScover]
    exact Measure.restrict_iUnion hSdisj hSmeas
  rw [hμsum, Measure.map_sum hh.aemeasurable, ← hsum]
  congr 1
  funext k
  exact tsm_map_restrict_congr μ (S k) hh (hhk k) (hagree k)

lemma tsm_measurable_selRand (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Measurable (atl_selRand μ σ f t s A) := by
  have hpair : Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      (acp_join t A p.1, p.2)) :=
    Measurable.prodMk
      ((ubfSplit n t).symm.measurable.comp (measurable_const.prodMk measurable_fst))
      measurable_snd
  have hstop : Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      stopVal μ σ f (acp_join t A p.1)) :=
    (measurable_stopVal μ σ f).comp
      ((ubfSplit n t).symm.measurable.comp (measurable_const.prodMk measurable_fst))
  have key : ∀ m : ℕ, Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      adaptWt (acp_join t A p.1) p.2 m s) :=
    fun m => (measurable_adaptWt_fixed m s).comp hpair
  have hglue : Measurable (fun mp : ℕ × (({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ)) =>
      adaptWt (acp_join t A mp.2.1) mp.2.2 mp.1 s) :=
    measurable_from_prod_countable_right key
  exact hglue.comp (hstop.prodMk measurable_id)

/-! ## B. Restricted sums -/

/-- The set of tail labels on which the stopping value equals `s`, given the head `A`. -/
def tsm_switchPiece (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (k : ℕ) :
    Set (({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ)) :=
  {p | stopVal μ σ f (acp_join t A p.1) = k}

lemma tsm_measurable_switch (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
        stopVal μ σ f (acp_join t A p.1)) := by
  have hjoin : Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      acp_join t A p.1) :=
    (ubfSplit n t).symm.measurable.comp (measurable_const.prodMk measurable_fst)
  exact (measurable_stopVal μ σ f).comp hjoin

lemma tsm_switchPiece_meas (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (k : ℕ) :
    MeasurableSet (tsm_switchPiece μ σ f t A k) :=
  (tsm_measurable_switch μ σ f t A) (measurableSet_singleton k)

lemma tsm_switchPiece_disj (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Pairwise (Function.onFun Disjoint (tsm_switchPiece μ σ f t A)) := by
  intro k l hkl
  refine Set.disjoint_left.mpr ?_
  intro p hpk hpl
  exact hkl (by rw [← (show stopVal μ σ f (acp_join t A p.1) = k from hpk),
    (show stopVal μ σ f (acp_join t A p.1) = l from hpl)])

lemma tsm_switchPiece_cover (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    ⋃ k, tsm_switchPiece μ σ f t A k = Set.univ := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨stopVal μ σ f (acp_join t A p.1), rfl⟩

lemma tsm_selRand_eq_on_piece (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (k : ℕ)
    (p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ))
    (hp : p ∈ tsm_switchPiece μ σ f t A k) :
    atl_selRand μ σ f t s A p = osp_tailSelFixed t s k A p := by
  change adaptWt (acp_join t A p.1) p.2 (stopVal μ σ f (acp_join t A p.1)) s
      = adaptWt (acp_join t A p.1) p.2 k s
  rw [show stopVal μ σ f (acp_join t A p.1) = k from hp]

/-- The restricted-sum identity for the tail selection on the switch piece. -/
def tsm_TailSelMP_restrictedSum (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) : Prop :=
  (Measure.sum (fun k => Measure.map (osp_tailSelFixed t s k A)
      (((ubfTail n t).prod (Vcube n)).restrict (tsm_switchPiece μ σ f t A k))))
    = Vcube n

lemma tsm_tailSelMP_of_restrictedSum (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (hres : tsm_TailSelMP_restrictedSum μ σ f t s A) :
    atl_TailSelMP μ σ f t s A := by
  change MeasurePreserving (atl_selRand μ σ f t s A) ((ubfTail n t).prod (Vcube n)) (Vcube n)
  exact tsm_measurePreserving_of_partition
    (S := tsm_switchPiece μ σ f t A)
    (tsm_switchPiece_meas μ σ f t A) (tsm_switchPiece_disj μ σ f t A)
    (tsm_switchPiece_cover μ σ f t A)
    (h := atl_selRand μ σ f t s A)
    (tsm_measurable_selRand μ σ f t s A)
    (hk := fun k => osp_tailSelFixed t s k A)
    (fun k => osp_tailSelFixed_meas t s k A)
    (fun k p hp => tsm_selRand_eq_on_piece μ σ f t s A k p hp)
    hres

lemma tsm_switchPiece_const_eq (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (k₀ : ℕ)
    (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) = k₀) :
    tsm_switchPiece μ σ f t A k₀ = Set.univ := by
  ext p
  simp only [tsm_switchPiece, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact hconst p.1

lemma tsm_switchPiece_const_empty (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (k₀ : ℕ)
    (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) = k₀)
    (k : ℕ) (hk : k ≠ k₀) :
    tsm_switchPiece μ σ f t A k = ∅ := by
  ext p
  simp only [tsm_switchPiece, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hpk
  exact hk (by rw [← hpk, hconst p.1])

lemma tsm_restrictedSum_of_const (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (t s : ℕ) (hts : t ≤ s) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (k₀ : ℕ) (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ,
        stopVal μ σ f (acp_join t A B) = k₀) :
    tsm_TailSelMP_restrictedSum μ σ f t s A := by
  change (Measure.sum (fun k => Measure.map (osp_tailSelFixed t s k A)
      (((ubfTail n t).prod (Vcube n)).restrict (tsm_switchPiece μ σ f t A k)))) = Vcube n
  have hzero : ∀ k, k ≠ k₀ → Measure.map (osp_tailSelFixed t s k A)
      (((ubfTail n t).prod (Vcube n)).restrict (tsm_switchPiece μ σ f t A k)) = 0 := by
    intro k hk
    rw [tsm_switchPiece_const_empty μ σ t A k₀ hconst k hk, Measure.restrict_empty,
      Measure.map_zero]
  rw [show (Measure.sum (fun k => Measure.map (osp_tailSelFixed t s k A)
        (((ubfTail n t).prod (Vcube n)).restrict (tsm_switchPiece μ σ f t A k))))
      = Measure.map (osp_tailSelFixed t s k₀ A)
        (((ubfTail n t).prod (Vcube n)).restrict (tsm_switchPiece μ σ f t A k₀)) from by
    ext T hT
    rw [Measure.sum_apply _ hT]
    exact tsum_eq_single k₀ (fun k hk => by rw [hzero k hk]; rfl)]
  rw [tsm_switchPiece_const_eq μ σ t A k₀ hconst, Measure.restrict_univ]
  exact (osp_tailSelFixed_mp t s k₀ hts A).map_eq

end AdaptDisintegration

end OSSS

end StatMech
