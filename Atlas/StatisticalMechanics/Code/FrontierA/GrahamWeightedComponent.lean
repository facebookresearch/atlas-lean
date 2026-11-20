/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Walls.gh4eq22
import Code.Sharpness.ClaimIsing
import Code.Sharpness.ClaimIsingFull
import Code.Sharpness.Claim1IsingFull
import Code.Sharpness.FluxEdgeCopyBridge

open Finset SimpleGraph
open scoped symmDiff

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Walls

variable {ι W : Type*} [DecidableEq ι] [Fintype ι]
  [DecidableEq W] [Fintype W]




noncomputable def grahamComponentComplement
    (ends : ι → Sym2 W) (m : Finset ι) (u : W) : Finset W :=
  notConnCompK ends m u


theorem grahamComponentComplement_not_mem
    (ends : ι → Sym2 W) (m : Finset ι) (u : W) :
    u ∉ grahamComponentComplement ends m u := by
  rw [grahamComponentComplement, mem_notConnCompK]
  exact not_not_intro Relation.ReflTransGen.refl



theorem grahamComponentComplement_noCrossing
    (ends : ι → Sym2 W) (m : Finset ι) (u : W) :
    NoCrossingK ends m (grahamComponentComplement ends m u) := by
  apply noCrossingK_of_event ends m _ u
  · exact grahamComponentComplement_not_mem ends m u
  · rfl



theorem grahamComponentComplement_noCrossing_of_subset
    (ends : ι → Sym2 W) (m K : Finset ι) (u : W) (hKm : K ⊆ m) :
    NoCrossingK ends K (grahamComponentComplement ends m u) := by
  intro i hi
  exact grahamComponentComplement_noCrossing ends m u i (hKm hi)


noncomputable def grahamSuperpositionBondComponent
    (ends : ι → Sym2 W) (m : Finset ι) (u : W) : Finset ι :=
  gh4_bondCompOf ends m u



theorem edgeInsideK_componentComplement_of_mem_sdiff
    (ends : ι → Sym2 W) (m : Finset ι) (u : W) {i : ι}
    (hi : i ∈ m \ grahamSuperpositionBondComponent ends m u) :
    edgeInsideK ends (grahamComponentComplement ends m u) i := by
  have him : i ∈ m := (Finset.mem_sdiff.mp hi).1
  have hnot : i ∉ grahamSuperpositionBondComponent ends m u :=
    (Finset.mem_sdiff.mp hi).2
  rcases grahamComponentComplement_noCrossing ends m u i him with hin | hout
  · exact hin
  · exfalso
    apply hnot
    rw [grahamSuperpositionBondComponent, gh4_mem_bondCompOf]
    refine ⟨him, ?_⟩
    obtain ⟨⟨a, b⟩, hab⟩ := (ends i).exists_rep
    refine ⟨a, hab ▸ Sym2.mem_mk_left a b, ?_⟩
    by_contra hconn
    have ha : a ∈ grahamComponentComplement ends m u := by
      rw [grahamComponentComplement, mem_notConnCompK]
      exact hconn
    exact (Finset.mem_compl.mp (hout a (hab ▸ Sym2.mem_mk_left a b))) ha



theorem mem_sdiff_component_of_edgeInsideK_complement
    (ends : ι → Sym2 W) (m : Finset ι) (u : W) {i : ι}
    (him : i ∈ m)
    (hi : edgeInsideK ends (grahamComponentComplement ends m u) i) :
    i ∈ m \ grahamSuperpositionBondComponent ends m u := by
  rw [Finset.mem_sdiff]
  refine ⟨him, ?_⟩
  intro hic
  rw [grahamSuperpositionBondComponent, gh4_mem_bondCompOf] at hic
  obtain ⟨_, x, hx, hconn⟩ := hic
  have hxout : x ∈ grahamComponentComplement ends m u := hi x hx
  rw [grahamComponentComplement, mem_notConnCompK] at hxout
  exact hxout hconn




theorem mem_sdiff_component_iff_edgeInsideK_complement
    (ends : ι → Sym2 W) (m : Finset ι) (u : W) {i : ι} :
    i ∈ m \ grahamSuperpositionBondComponent ends m u ↔
      i ∈ m ∧ edgeInsideK ends (grahamComponentComplement ends m u) i := by
  constructor
  · intro hi
    exact ⟨(Finset.mem_sdiff.mp hi).1,
      edgeInsideK_componentComplement_of_mem_sdiff ends m u hi⟩
  · rintro ⟨him, hi⟩
    exact mem_sdiff_component_of_edgeInsideK_complement ends m u him hi

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem couplingIn_componentComplement_endsM
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V → ℝ) (m : ↥G.edgeFinset → ℕ) (u : V)
    {i : Copy G m}
    (hi : i ∈ (Finset.univ : Finset (Copy G m)) \
      grahamSuperpositionBondComponent (endsM G m) Finset.univ u) :
    StatMech.Sharpness.couplingIn J
        (grahamComponentComplement (endsM G m) Finset.univ u)
        (endsM G m i) = J (endsM G m i) := by
  unfold StatMech.Sharpness.couplingIn
  rw [if_pos]
  exact edgeInsideK_componentComplement_of_mem_sdiff
    (endsM G m) Finset.univ u hi



theorem couplingIn_componentComplement_eq_zero_of_mem_component
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V → ℝ) (m : ↥G.edgeFinset → ℕ) (u : V)
    {i : Copy G m}
    (hi : i ∈ grahamSuperpositionBondComponent (endsM G m) Finset.univ u) :
    StatMech.Sharpness.couplingIn J
        (grahamComponentComplement (endsM G m) Finset.univ u)
        (endsM G m i) = 0 := by
  unfold StatMech.Sharpness.couplingIn
  rw [if_neg]
  intro hin
  have hsd : i ∈ (Finset.univ : Finset (Copy G m)) \
      grahamSuperpositionBondComponent (endsM G m) Finset.univ u :=
    mem_sdiff_component_of_edgeInsideK_complement
      (endsM G m) Finset.univ u (Finset.mem_univ i) hin
  exact (Finset.mem_sdiff.mp hsd).2 hi

end StatMech.FrontierA
