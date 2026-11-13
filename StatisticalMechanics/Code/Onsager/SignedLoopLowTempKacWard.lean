/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopLowTempDual
import Code.FrontierA.KacWardArbitraryValenceClosure











open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice
open StatMech.FrontierA

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

noncomputable instance kwg_subdivGraph_decidableAdj (ends : E -> Sym2 V) :
    DecidableRel (kwg_subdivGraph ends).Adj := Classical.decRel _

abbrev kwg_SubdivEdge (V E : Type*) := Sym2 (kwg_SubdivVertex V E)


def kwg_subdivLeftEdge (ends : E -> Sym2 V) (e : E) : kwg_SubdivEdge V E :=
  s(Sum.inl (ends e).out.1, Sum.inr (e, false))


def kwg_subdivCentralEdge (e : E) : kwg_SubdivEdge V E :=
  s(Sum.inr (e, false), Sum.inr (e, true))


def kwg_subdivRightEdge (ends : E -> Sym2 V) (e : E) : kwg_SubdivEdge V E :=
  s(Sum.inr (e, true), Sum.inl (ends e).out.2)


def kwg_subdivGadgetEdges (ends : E -> Sym2 V) (e : E) :
    Finset (kwg_SubdivEdge V E) :=
  {kwg_subdivLeftEdge ends e, kwg_subdivCentralEdge e,
    kwg_subdivRightEdge ends e}


def kwg_subdivLift (ends : E -> Sym2 V) (F : Finset E) :
    Finset (kwg_SubdivEdge V E) :=
  F.biUnion (kwg_subdivGadgetEdges ends)



def kwg_subdivWeight (x : E -> ℂ) : kwg_SubdivEdge V E -> ℂ :=
  fun edge => if h : ∃ e : E, kwg_subdivCentralEdge e = edge
    then x h.choose else 1

@[simp] theorem kwg_subdivCentralEdge_injective :
    Function.Injective (kwg_subdivCentralEdge : E -> kwg_SubdivEdge V E) := by
  intro e e' h
  unfold kwg_subdivCentralEdge at h
  rw [Sym2.eq_iff] at h
  rcases h with h | h <;> simp only [Sum.inr.injEq, Prod.mk.injEq,
    Bool.false_eq_true, Bool.true_eq_false, and_false] at h
  exact h.1.1

@[simp] theorem kwg_subdivCentralEdge_mem_gadget (ends : E -> Sym2 V)
    (e e' : E) :
    kwg_subdivCentralEdge e' ∈ kwg_subdivGadgetEdges ends e ↔ e' = e := by
  simp only [kwg_subdivGadgetEdges, Finset.mem_insert, Finset.mem_singleton]
  unfold kwg_subdivCentralEdge kwg_subdivLeftEdge kwg_subdivRightEdge
  rw [Sym2.eq_iff, Sym2.eq_iff, Sym2.eq_iff]
  simp

@[simp] theorem kwg_subdivCentralEdge_mem_lift (ends : E -> Sym2 V)
    (F : Finset E) (e : E) :
    kwg_subdivCentralEdge e ∈ kwg_subdivLift ends F ↔ e ∈ F := by
  simp [kwg_subdivLift]



theorem kwg_subdivGraph_mem_edgeFinset_iff (ends : E -> Sym2 V)
    (edge : kwg_SubdivEdge V E) :
    edge ∈ (kwg_subdivGraph ends).edgeFinset ↔
      ∃ e : E, edge ∈ kwg_subdivGadgetEdges ends e := by
  induction edge using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      rcases a with v | ⟨e, c⟩ <;> rcases b with w | ⟨e', c'⟩
      · simp only [kwg_subdivGraph, false_iff, not_exists]
        intro e
        simp [kwg_subdivGadgetEdges, kwg_subdivLeftEdge,
          kwg_subdivCentralEdge, kwg_subdivRightEdge, Sym2.eq_iff]
      · cases c' <;>
          simp [kwg_subdivGraph, kwg_subdivGadgetEdges,
            kwg_subdivLeftEdge, kwg_subdivCentralEdge,
            kwg_subdivRightEdge, Sym2.eq_iff]
      · cases c <;>
          simp [kwg_subdivGraph, kwg_subdivGadgetEdges,
            kwg_subdivLeftEdge, kwg_subdivCentralEdge,
            kwg_subdivRightEdge, Sym2.eq_iff, eq_comm]
      · cases c <;> cases c' <;>
          simp [kwg_subdivGraph, kwg_subdivGadgetEdges,
            kwg_subdivLeftEdge, kwg_subdivCentralEdge,
            kwg_subdivRightEdge, Sym2.eq_iff, eq_comm]

theorem kwg_subdivLift_subset_edgeFinset (ends : E -> Sym2 V)
    (F : Finset E) :
    kwg_subdivLift ends F ⊆ (kwg_subdivGraph ends).edgeFinset := by
  intro edge hedge
  rw [kwg_subdivGraph_mem_edgeFinset_iff]
  unfold kwg_subdivLift at hedge
  rw [Finset.mem_biUnion] at hedge
  exact ⟨hedge.choose, hedge.choose_spec.2⟩

@[simp] theorem kwg_subdivGraph_neighborFinset_false
    (ends : E -> Sym2 V) (e : E) :
    (kwg_subdivGraph ends).neighborFinset (Sum.inr (e, false)) =
      {Sum.inl (ends e).out.1, Sum.inr (e, true)} := by
  ext z
  rw [SimpleGraph.mem_neighborFinset]
  rcases z with v | ⟨e', b⟩
  · simp [kwg_subdivGraph, eq_comm]
  · cases b <;> simp [kwg_subdivGraph, eq_comm]

@[simp] theorem kwg_subdivGraph_neighborFinset_true
    (ends : E -> Sym2 V) (e : E) :
    (kwg_subdivGraph ends).neighborFinset (Sum.inr (e, true)) =
      {Sum.inr (e, false), Sum.inl (ends e).out.2} := by
  ext z
  rw [SimpleGraph.mem_neighborFinset]
  rcases z with v | ⟨e', b⟩
  · simp [kwg_subdivGraph, eq_comm]
  · cases b <;> simp [kwg_subdivGraph, eq_comm]



theorem kwg_evenSubgraph_gadget_membership (ends : E -> Sym2 V)
    (H : Finset (kwg_SubdivEdge V E))
    (hH : H ∈ evenSubgraphs (kwg_subdivGraph ends)) (e : E) :
    kwg_subdivLeftEdge ends e ∈ H ↔ kwg_subdivCentralEdge e ∈ H := by
  letI : SimpleGraph.LocallyFinite (kwg_subdivGraph ends) :=
    fun _ => Subtype.fintype _
  have hsum := kw_evenSubgraph_neighbor_sum_zero
    (kwg_subdivGraph ends) H hH (Sum.inr (e, false))
  have hsum' :
      (∑ w ∈ ({Sum.inl (ends e).out.1, Sum.inr (e, true)} :
          Finset (kwg_SubdivVertex V E)),
        if s(Sum.inr (e, false), w) ∈ H then (1 : ZMod 2) else 0) = 0 := by
    calc
      _ = ∑ w ∈ (kwg_subdivGraph ends).neighborFinset
          (Sum.inr (e, false)),
          if s(Sum.inr (e, false), w) ∈ H then (1 : ZMod 2) else 0 := by
        apply Finset.sum_congr
        · ext z
          rw [SimpleGraph.mem_neighborFinset]
          rcases z with v | ⟨e', b⟩
          · simp [kwg_subdivGraph, eq_comm]
          · cases b <;> simp [kwg_subdivGraph, eq_comm]
        · intros
          rfl
      _ = 0 := hsum
  have hparity :
      (if kwg_subdivLeftEdge ends e ∈ H then (1 : ZMod 2) else 0) +
        (if kwg_subdivCentralEdge e ∈ H then 1 else 0) = 0 := by
    rw [Finset.sum_insert (by simp), Finset.sum_singleton] at hsum'
    simpa only [kwg_subdivLeftEdge, kwg_subdivCentralEdge,
      Sym2.eq_swap] using hsum'
  by_cases hl : kwg_subdivLeftEdge ends e ∈ H <;>
    by_cases hc : kwg_subdivCentralEdge e ∈ H <;> simp [hl, hc] at hparity ⊢

theorem kwg_evenSubgraph_gadget_membership_right (ends : E -> Sym2 V)
    (H : Finset (kwg_SubdivEdge V E))
    (hH : H ∈ evenSubgraphs (kwg_subdivGraph ends)) (e : E) :
    kwg_subdivRightEdge ends e ∈ H ↔ kwg_subdivCentralEdge e ∈ H := by
  letI : SimpleGraph.LocallyFinite (kwg_subdivGraph ends) :=
    fun _ => Subtype.fintype _
  have hsum := kw_evenSubgraph_neighbor_sum_zero
    (kwg_subdivGraph ends) H hH (Sum.inr (e, true))
  have hsum' :
      (∑ w ∈ ({Sum.inr (e, false), Sum.inl (ends e).out.2} :
          Finset (kwg_SubdivVertex V E)),
        if s(Sum.inr (e, true), w) ∈ H then (1 : ZMod 2) else 0) = 0 := by
    calc
      _ = ∑ w ∈ (kwg_subdivGraph ends).neighborFinset
          (Sum.inr (e, true)),
          if s(Sum.inr (e, true), w) ∈ H then (1 : ZMod 2) else 0 := by
        apply Finset.sum_congr
        · ext z
          rw [SimpleGraph.mem_neighborFinset]
          rcases z with v | ⟨e', b⟩
          · simp [kwg_subdivGraph, eq_comm]
          · cases b <;> simp [kwg_subdivGraph, eq_comm]
        · intros
          rfl
      _ = 0 := hsum
  have hparity :
      (if kwg_subdivCentralEdge e ∈ H then (1 : ZMod 2) else 0) +
        (if kwg_subdivRightEdge ends e ∈ H then 1 else 0) = 0 := by
    rw [Finset.sum_insert (by simp), Finset.sum_singleton] at hsum'
    simpa only [kwg_subdivCentralEdge, kwg_subdivRightEdge,
      Sym2.eq_swap] using hsum'
  by_cases hr : kwg_subdivRightEdge ends e ∈ H <;>
    by_cases hc : kwg_subdivCentralEdge e ∈ H <;> simp [hr, hc] at hparity ⊢


def kwg_subdivExtract (H : Finset (kwg_SubdivEdge V E)) : Finset E :=
  Finset.univ.filter fun e => kwg_subdivCentralEdge e ∈ H

@[simp] theorem kwg_subdivExtract_lift (ends : E -> Sym2 V)
    (F : Finset E) :
    kwg_subdivExtract (kwg_subdivLift ends F) = F := by
  ext e
  simp [kwg_subdivExtract]



theorem kwg_subdivLift_extract_of_even (ends : E -> Sym2 V)
    (H : Finset (kwg_SubdivEdge V E))
    (hH : H ∈ evenSubgraphs (kwg_subdivGraph ends)) :
    kwg_subdivLift ends (kwg_subdivExtract H) = H := by
  have hdata := hH
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
  ext edge
  constructor
  · intro hedge
    unfold kwg_subdivLift at hedge
    rw [Finset.mem_biUnion] at hedge
    obtain ⟨e, he, hedge⟩ := hedge
    have hc : kwg_subdivCentralEdge e ∈ H := by
      simpa [kwg_subdivExtract] using he
    simp only [kwg_subdivGadgetEdges, Finset.mem_insert,
      Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl | rfl
    · exact (kwg_evenSubgraph_gadget_membership ends H hH e).mpr hc
    · exact hc
    · exact (kwg_evenSubgraph_gadget_membership_right ends H hH e).mpr hc
  · intro hedge
    have hedgeGraph := hdata.1 hedge
    rw [kwg_subdivGraph_mem_edgeFinset_iff] at hedgeGraph
    obtain ⟨e, he⟩ := hedgeGraph
    have hc : kwg_subdivCentralEdge e ∈ H := by
      simp only [kwg_subdivGadgetEdges, Finset.mem_insert,
        Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact (kwg_evenSubgraph_gadget_membership ends H hH e).mp hedge
      · exact hedge
      · exact (kwg_evenSubgraph_gadget_membership_right ends H hH e).mp hedge
    unfold kwg_subdivLift
    rw [Finset.mem_biUnion]
    exact ⟨e, by simp [kwg_subdivExtract, hc], he⟩

private theorem kwg_subdivLeftEdge_injective (ends : E -> Sym2 V) :
    Function.Injective (kwg_subdivLeftEdge ends) := by
  intro e e' h
  unfold kwg_subdivLeftEdge at h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · simpa using congrArg (fun z => z.1) (Sum.inr.inj h.2)
  · simp at h

private theorem kwg_subdivRightEdge_injective (ends : E -> Sym2 V) :
    Function.Injective (kwg_subdivRightEdge ends) := by
  intro e e' h
  unfold kwg_subdivRightEdge at h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · simpa using congrArg (fun z => z.1) (Sum.inr.inj h.1)
  · simp at h

@[simp] theorem kwg_subdivLeftEdge_mem_lift (ends : E -> Sym2 V)
    (F : Finset E) (e : E) :
    kwg_subdivLeftEdge ends e ∈ kwg_subdivLift ends F ↔ e ∈ F := by
  constructor
  · intro h
    unfold kwg_subdivLift at h
    rw [Finset.mem_biUnion] at h
    obtain ⟨e', he', hedge⟩ := h
    simp only [kwg_subdivGadgetEdges, Finset.mem_insert,
      Finset.mem_singleton] at hedge
    rcases hedge with hedge | hedge | hedge
    · exact (kwg_subdivLeftEdge_injective ends hedge).symm ▸ he'
    · unfold kwg_subdivLeftEdge kwg_subdivCentralEdge at hedge
      rw [Sym2.eq_iff] at hedge
      rcases hedge with h | h <;> simp at h
    · unfold kwg_subdivLeftEdge kwg_subdivRightEdge at hedge
      rw [Sym2.eq_iff] at hedge
      rcases hedge with h | h <;> simp at h
  · intro he
    unfold kwg_subdivLift
    rw [Finset.mem_biUnion]
    exact ⟨e, he, by simp [kwg_subdivGadgetEdges]⟩

@[simp] theorem kwg_subdivRightEdge_mem_lift (ends : E -> Sym2 V)
    (F : Finset E) (e : E) :
    kwg_subdivRightEdge ends e ∈ kwg_subdivLift ends F ↔ e ∈ F := by
  constructor
  · intro h
    unfold kwg_subdivLift at h
    rw [Finset.mem_biUnion] at h
    obtain ⟨e', he', hedge⟩ := h
    simp only [kwg_subdivGadgetEdges, Finset.mem_insert,
      Finset.mem_singleton] at hedge
    rcases hedge with hedge | hedge | hedge
    · unfold kwg_subdivRightEdge kwg_subdivLeftEdge at hedge
      rw [Sym2.eq_iff] at hedge
      rcases hedge with h | h <;> simp at h
    · unfold kwg_subdivRightEdge kwg_subdivCentralEdge at hedge
      rw [Sym2.eq_iff] at hedge
      rcases hedge with h | h <;> simp at h
    · exact (kwg_subdivRightEdge_injective ends hedge).symm ▸ he'
  · intro he
    unfold kwg_subdivLift
    rw [Finset.mem_biUnion]
    exact ⟨e, he, by simp [kwg_subdivGadgetEdges]⟩

private theorem kwg_subdivLeft_right_disjoint (ends : E -> Sym2 V)
    (A B : Finset E) :
    Disjoint (A.image (kwg_subdivLeftEdge ends))
      (B.image (kwg_subdivRightEdge ends)) := by
  rw [Finset.disjoint_left]
  intro edge hleft hright
  rw [Finset.mem_image] at hleft hright
  obtain ⟨e, _, rfl⟩ := hleft
  obtain ⟨e', _, heq⟩ := hright
  unfold kwg_subdivLeftEdge kwg_subdivRightEdge at heq
  rw [Sym2.eq_iff] at heq
  rcases heq with h | h <;> simp at h

theorem kwg_incCount_subdivLift_face (ends : E -> Sym2 V)
    (F : Finset E) (v : V) :
    incCount (kwg_subdivLift ends F) (Sum.inl v) =
      (F.filter (fun e => (ends e).out.1 = v)).card +
        (F.filter (fun e => (ends e).out.2 = v)).card := by
  let A := F.filter (fun e => (ends e).out.1 = v)
  let B := F.filter (fun e => (ends e).out.2 = v)
  have hfilter :
      (kwg_subdivLift ends F).filter (fun edge => Sum.inl v ∈ edge) =
        A.image (kwg_subdivLeftEdge ends) ∪
          B.image (kwg_subdivRightEdge ends) := by
    ext edge
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hedge, hinc⟩
      unfold kwg_subdivLift at hedge
      rw [Finset.mem_biUnion] at hedge
      obtain ⟨e, heF, he⟩ := hedge
      simp only [kwg_subdivGadgetEdges, Finset.mem_insert,
        Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · left
        refine ⟨e, ?_, rfl⟩
        rw [Finset.mem_filter]
        refine ⟨heF, ?_⟩
        have hv : v = (ends e).out.1 := by
          simpa [kwg_subdivLeftEdge] using hinc
        exact hv.symm
      · simp [kwg_subdivCentralEdge] at hinc
      · right
        refine ⟨e, ?_, rfl⟩
        rw [Finset.mem_filter]
        refine ⟨heF, ?_⟩
        have hv : v = (ends e).out.2 := by
          simpa [kwg_subdivRightEdge] using hinc
        exact hv.symm
    · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
      · rw [Finset.mem_filter] at he
        constructor
        · unfold kwg_subdivLift
          rw [Finset.mem_biUnion]
          exact ⟨e, he.1, by simp [kwg_subdivGadgetEdges]⟩
        · simpa [kwg_subdivLeftEdge] using he.2.symm
      · rw [Finset.mem_filter] at he
        constructor
        · unfold kwg_subdivLift
          rw [Finset.mem_biUnion]
          exact ⟨e, he.1, by simp [kwg_subdivGadgetEdges]⟩
        · simpa [kwg_subdivRightEdge] using he.2.symm
  unfold incCount
  rw [hfilter, Finset.card_union_of_disjoint
    (kwg_subdivLeft_right_disjoint ends A B),
    Finset.card_image_of_injective _ (kwg_subdivLeftEdge_injective ends),
    Finset.card_image_of_injective _ (kwg_subdivRightEdge_injective ends)]

private theorem kwg_subdivGraph_incident_false_iff (ends : E -> Sym2 V)
    (e : E) (edge : kwg_SubdivEdge V E) :
    edge ∈ (kwg_subdivGraph ends).edgeFinset ∧ Sum.inr (e, false) ∈ edge ↔
      edge = kwg_subdivLeftEdge ends e ∨ edge = kwg_subdivCentralEdge e := by
  induction edge using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      rcases a with v | ⟨e', c⟩ <;> rcases b with w | ⟨e'', c'⟩
      · simp [kwg_subdivGraph, kwg_subdivLeftEdge,
          kwg_subdivCentralEdge, Sym2.eq_iff]
      · cases c' <;> simp [kwg_subdivGraph, kwg_subdivLeftEdge,
          kwg_subdivCentralEdge, Sym2.eq_iff, eq_comm] <;> grind
      · cases c <;> simp [kwg_subdivGraph, kwg_subdivLeftEdge,
          kwg_subdivCentralEdge, Sym2.eq_iff, eq_comm] <;> grind
      · cases c <;> cases c' <;> simp [kwg_subdivGraph,
          kwg_subdivLeftEdge, kwg_subdivCentralEdge, Sym2.eq_iff, eq_comm] <;> grind

private theorem kwg_subdivGraph_incident_true_iff (ends : E -> Sym2 V)
    (e : E) (edge : kwg_SubdivEdge V E) :
    edge ∈ (kwg_subdivGraph ends).edgeFinset ∧ Sum.inr (e, true) ∈ edge ↔
      edge = kwg_subdivCentralEdge e ∨ edge = kwg_subdivRightEdge ends e := by
  induction edge using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      rcases a with v | ⟨e', c⟩ <;> rcases b with w | ⟨e'', c'⟩
      · simp [kwg_subdivGraph, kwg_subdivCentralEdge,
          kwg_subdivRightEdge, Sym2.eq_iff]
      · cases c' <;> simp [kwg_subdivGraph, kwg_subdivCentralEdge,
          kwg_subdivRightEdge, Sym2.eq_iff, eq_comm] <;> grind
      · cases c <;> simp [kwg_subdivGraph, kwg_subdivCentralEdge,
          kwg_subdivRightEdge, Sym2.eq_iff, eq_comm] <;> grind
      · cases c <;> cases c' <;> simp [kwg_subdivGraph,
          kwg_subdivCentralEdge, kwg_subdivRightEdge, Sym2.eq_iff, eq_comm] <;> grind

theorem kwg_incCount_subdivLift_port (ends : E -> Sym2 V)
    (F : Finset E) (e : E) (b : Bool) :
    incCount (kwg_subdivLift ends F) (Sum.inr (e, b)) =
      if e ∈ F then 2 else 0 := by
  cases b
  · have hfilter :
        (kwg_subdivLift ends F).filter
            (fun edge => Sum.inr (e, false) ∈ edge) =
          if e ∈ F then
            {kwg_subdivLeftEdge ends e, kwg_subdivCentralEdge e} else ∅ := by
      ext edge
      by_cases he : e ∈ F
      · simp only [he, if_true, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨hedge, hinc⟩
          exact (kwg_subdivGraph_incident_false_iff ends e edge).mp
            ⟨kwg_subdivLift_subset_edgeFinset ends F hedge, hinc⟩
        · intro hedge
          rcases hedge with rfl | rfl
          · exact ⟨by
                unfold kwg_subdivLift
                rw [Finset.mem_biUnion]
                exact ⟨e, he, by simp [kwg_subdivGadgetEdges]⟩,
              by simp [kwg_subdivLeftEdge]⟩
          · exact ⟨by
                unfold kwg_subdivLift
                rw [Finset.mem_biUnion]
                exact ⟨e, he, by simp [kwg_subdivGadgetEdges]⟩,
              by simp [kwg_subdivCentralEdge]⟩
      · rw [if_neg he]
        rw [Finset.mem_filter]
        rw [show edge ∈ (∅ : Finset (kwg_SubdivEdge V E)) ↔ False by simp]
        rw [iff_false]
        rintro ⟨hedge, hinc⟩
        have hcases := (kwg_subdivGraph_incident_false_iff ends e edge).mp
          ⟨kwg_subdivLift_subset_edgeFinset ends F hedge, hinc⟩
        rcases hcases with rfl | rfl
        · exact he ((kwg_subdivLeftEdge_mem_lift ends F e).mp hedge)
        · exact he ((kwg_subdivCentralEdge_mem_lift ends F e).mp hedge)
    unfold incCount
    rw [hfilter]
    split_ifs with he
    · simp [kwg_subdivLeftEdge, kwg_subdivCentralEdge, Sym2.eq_iff]
    · rfl
  · have hfilter :
        (kwg_subdivLift ends F).filter
            (fun edge => Sum.inr (e, true) ∈ edge) =
          if e ∈ F then
            {kwg_subdivCentralEdge e, kwg_subdivRightEdge ends e} else ∅ := by
      ext edge
      by_cases he : e ∈ F
      · simp only [he, if_true, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨hedge, hinc⟩
          exact (kwg_subdivGraph_incident_true_iff ends e edge).mp
            ⟨kwg_subdivLift_subset_edgeFinset ends F hedge, hinc⟩
        · intro hedge
          rcases hedge with rfl | rfl
          · exact ⟨by
                unfold kwg_subdivLift
                rw [Finset.mem_biUnion]
                exact ⟨e, he, by simp [kwg_subdivGadgetEdges]⟩,
              by simp [kwg_subdivCentralEdge]⟩
          · exact ⟨by
                unfold kwg_subdivLift
                rw [Finset.mem_biUnion]
                exact ⟨e, he, by simp [kwg_subdivGadgetEdges]⟩,
              by simp [kwg_subdivRightEdge]⟩
      · rw [if_neg he]
        rw [Finset.mem_filter]
        rw [show edge ∈ (∅ : Finset (kwg_SubdivEdge V E)) ↔ False by simp]
        rw [iff_false]
        rintro ⟨hedge, hinc⟩
        have hcases := (kwg_subdivGraph_incident_true_iff ends e edge).mp
          ⟨kwg_subdivLift_subset_edgeFinset ends F hedge, hinc⟩
        rcases hcases with rfl | rfl
        · exact he ((kwg_subdivCentralEdge_mem_lift ends F e).mp hedge)
        · exact he ((kwg_subdivRightEdge_mem_lift ends F e).mp hedge)
    unfold incCount
    rw [hfilter]
    split_ifs with he
    · simp [kwg_subdivCentralEdge, kwg_subdivRightEdge, Sym2.eq_iff]
    · rfl

private theorem kwg_subdiv_card_filter_eq_sum_ite
    (F : Finset E) (p : E -> Prop) [DecidablePred p] :
    (F.filter p).card = ∑ e ∈ F, if p e then 1 else 0 := by
  induction F using Finset.induction with
  | empty => simp
  | @insert e F he ih =>
      by_cases hp : p e <;> simp [he, hp, ih]

private theorem kwg_endpointCount_even_iff (ends : E -> Sym2 V)
    (F : Finset E) (v : V) :
    Even ((F.filter (fun e => (ends e).out.1 = v)).card +
      (F.filter (fun e => (ends e).out.2 = v)).card) ↔
      Even (kwg_degree ends F v) := by
  let A := F.filter (fun e => (ends e).out.1 = v)
  let B := F.filter (fun e => (ends e).out.2 = v)
  let I := F.filter (fun e => kwg_incidentMod2 v (ends e))
  let L := F.filter
    (fun e => (ends e).out.1 = v ∧ (ends e).out.2 = v)
  have hcount : A.card + B.card = I.card + 2 * L.card := by
    rw [kwg_subdiv_card_filter_eq_sum_ite,
      kwg_subdiv_card_filter_eq_sum_ite,
      kwg_subdiv_card_filter_eq_sum_ite,
      kwg_subdiv_card_filter_eq_sum_ite]
    rw [← Finset.sum_add_distrib]
    calc
      ∑ e ∈ F, ((if (ends e).out.1 = v then 1 else 0) +
          if (ends e).out.2 = v then 1 else 0) =
          ∑ e ∈ F, ((if kwg_incidentMod2 v (ends e) then 1 else 0) +
            2 * if (ends e).out.1 = v ∧ (ends e).out.2 = v then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro e _
        have hout : ends e = s((ends e).out.1, (ends e).out.2) :=
          (ends e).out_eq.symm
        have hinc : kwg_incidentMod2 v (ends e) ↔
            ((ends e).out.1 = v ∧ (ends e).out.2 ≠ v) ∨
              ((ends e).out.2 = v ∧ (ends e).out.1 ≠ v) := by
          conv_lhs => rw [hout]
          exact kwg_incidentMod2_mk v (ends e).out.1 (ends e).out.2
        by_cases h1 : (ends e).out.1 = v <;>
          by_cases h2 : (ends e).out.2 = v <;> simp [hinc, h1, h2]
      _ = (∑ e ∈ F, if kwg_incidentMod2 v (ends e) then 1 else 0) +
          ∑ e ∈ F, 2 * if (ends e).out.1 = v ∧
            (ends e).out.2 = v then 1 else 0 := by
        rw [Finset.sum_add_distrib]
      _ = (∑ e ∈ F, if kwg_incidentMod2 v (ends e) then 1 else 0) +
          2 * ∑ e ∈ F, if (ends e).out.1 = v ∧
            (ends e).out.2 = v then 1 else 0 := by
        rw [Finset.mul_sum]
  change Even (A.card + B.card) ↔ Even I.card
  rw [hcount]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k - L.card, ?_⟩
    omega
  · rintro ⟨k, hk⟩
    refine ⟨k + L.card, ?_⟩
    omega



theorem kwg_subdivLift_isEven_iff (ends : E -> Sym2 V) (F : Finset E) :
    IsEvenSubgraph (kwg_subdivLift ends F) ↔ kwg_IsEven ends F := by
  constructor
  · intro h v
    have hv := h (Sum.inl v)
    rw [kwg_incCount_subdivLift_face] at hv
    exact (kwg_endpointCount_even_iff ends F v).mp hv
  · intro h z
    rcases z with v | ⟨e, b⟩
    · rw [kwg_incCount_subdivLift_face]
      exact (kwg_endpointCount_even_iff ends F v).mpr (h v)
    · rw [kwg_incCount_subdivLift_port]
      split_ifs <;> norm_num

theorem kwg_subdivLift_mem_evenSubgraphs_iff (ends : E -> Sym2 V)
    (F : Finset E) :
    kwg_subdivLift ends F ∈ evenSubgraphs (kwg_subdivGraph ends) ↔
      kwg_IsEven ends F := by
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset]
  exact and_iff_right (kwg_subdivLift_subset_edgeFinset ends F) |>.trans
    (kwg_subdivLift_isEven_iff ends F)


def KWGIndexedEvenSet (ends : E -> Sym2 V) :=
  {F : Finset E // kwg_IsEven ends F}

noncomputable instance kwgIndexedEvenSetFintype (ends : E -> Sym2 V) :
    Fintype (KWGIndexedEvenSet ends) := by
  classical
  unfold KWGIndexedEvenSet
  apply Fintype.ofFinset (Finset.univ.filter (kwg_IsEven ends))
  intro F
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl



noncomputable def kwg_subdivEvenEquiv (ends : E -> Sym2 V) :
    KWGIndexedEvenSet ends ≃ KWActualEvenSubgraph (kwg_subdivGraph ends) where
  toFun F := ⟨kwg_subdivLift ends F.1,
    (kwg_subdivLift_mem_evenSubgraphs_iff ends F.1).mpr F.2⟩
  invFun H := ⟨kwg_subdivExtract H.1, by
    have hH := H.2
    rw [← kwg_subdivLift_extract_of_even ends H.1 H.2] at hH
    exact (kwg_subdivLift_mem_evenSubgraphs_iff ends _).mp hH⟩
  left_inv F := by
    apply Subtype.ext
    exact kwg_subdivExtract_lift ends F.1
  right_inv H := by
    apply Subtype.ext
    exact kwg_subdivLift_extract_of_even ends H.1 H.2

@[simp] theorem kwg_subdivWeight_central (x : E -> ℂ) (e : E) :
    (kwg_subdivWeight (V := V) x) (kwg_subdivCentralEdge e) = x e := by
  unfold kwg_subdivWeight
  split
  · rename_i h
    congr 1
    apply kwg_subdivCentralEdge_injective (V := V) (E := E)
    exact h.choose_spec
  · rename_i h
    exact (h ⟨e, rfl⟩).elim

@[simp] theorem kwg_subdivWeight_left (ends : E -> Sym2 V)
    (x : E -> ℂ) (e : E) :
    (kwg_subdivWeight (V := V) x) (kwg_subdivLeftEdge ends e) = 1 := by
  unfold kwg_subdivWeight
  rw [dif_neg]
  rintro ⟨e', heq⟩
  unfold kwg_subdivCentralEdge kwg_subdivLeftEdge at heq
  rw [Sym2.eq_iff] at heq
  rcases heq with h | h <;> simp at h

@[simp] theorem kwg_subdivWeight_right (ends : E -> Sym2 V)
    (x : E -> ℂ) (e : E) :
    (kwg_subdivWeight (V := V) x) (kwg_subdivRightEdge ends e) = 1 := by
  unfold kwg_subdivWeight
  rw [dif_neg]
  rintro ⟨e', heq⟩
  unfold kwg_subdivCentralEdge kwg_subdivRightEdge at heq
  rw [Sym2.eq_iff] at heq
  rcases heq with h | h <;> simp at h

private theorem kwg_subdivGadget_owner_unique (ends : E -> Sym2 V)
    {e e' : E} {edge : kwg_SubdivEdge V E}
    (he : edge ∈ kwg_subdivGadgetEdges ends e)
    (he' : edge ∈ kwg_subdivGadgetEdges ends e') : e = e' := by
  simp only [kwg_subdivGadgetEdges, Finset.mem_insert,
    Finset.mem_singleton] at he he'
  rcases he with rfl | rfl | rfl <;> rcases he' with h | h | h
  · exact kwg_subdivLeftEdge_injective ends h
  · exfalso
    unfold kwg_subdivLeftEdge kwg_subdivCentralEdge at h
    rw [Sym2.eq_iff] at h
    rcases h with h | h <;> simp at h
  · exfalso
    unfold kwg_subdivLeftEdge kwg_subdivRightEdge at h
    rw [Sym2.eq_iff] at h
    rcases h with h | h <;> simp at h
  · exfalso
    unfold kwg_subdivCentralEdge kwg_subdivLeftEdge at h
    rw [Sym2.eq_iff] at h
    rcases h with h | h <;> simp at h
  · exact kwg_subdivCentralEdge_injective h
  · exfalso
    unfold kwg_subdivCentralEdge kwg_subdivRightEdge at h
    rw [Sym2.eq_iff] at h
    rcases h with h | h <;> simp at h
  · exfalso
    unfold kwg_subdivRightEdge kwg_subdivLeftEdge at h
    rw [Sym2.eq_iff] at h
    rcases h with h | h <;> simp at h
  · exfalso
    unfold kwg_subdivRightEdge kwg_subdivCentralEdge at h
    rw [Sym2.eq_iff] at h
    rcases h with h | h <;> simp at h
  · exact kwg_subdivRightEdge_injective ends h

private theorem kwg_subdivGadgets_pairwiseDisjoint (ends : E -> Sym2 V)
    (F : Finset E) :
    (↑F : Set E).PairwiseDisjoint (kwg_subdivGadgetEdges ends) := by
  intro e _ e' _ hne
  change Disjoint (kwg_subdivGadgetEdges ends e)
    (kwg_subdivGadgetEdges ends e')
  rw [Finset.disjoint_left]
  intro edge he he'
  exact hne (kwg_subdivGadget_owner_unique ends he he')

theorem kwg_subdivLift_weight_product (ends : E -> Sym2 V)
    (x : E -> ℂ) (F : Finset E) :
    ∏ edge ∈ kwg_subdivLift ends F, kwg_subdivWeight (V := V) x edge =
      ∏ e ∈ F, x e := by
  unfold kwg_subdivLift
  rw [Finset.prod_biUnion (kwg_subdivGadgets_pairwiseDisjoint ends F)]
  apply Finset.prod_congr rfl
  intro e _
  unfold kwg_subdivGadgetEdges
  rw [Finset.prod_insert (by
      simp [kwg_subdivLeftEdge, kwg_subdivCentralEdge,
        kwg_subdivRightEdge, Sym2.eq_iff]),
    Finset.prod_insert (by
      simp [kwg_subdivCentralEdge, kwg_subdivRightEdge, Sym2.eq_iff]),
    Finset.prod_singleton]
  simp


noncomputable def kwg_indexedEvenPolynomial (ends : E -> Sym2 V)
    (x : E -> ℂ) : ℂ :=
  ∑ F : Finset E,
    if kwg_IsEven ends F then ∏ e ∈ F, x e else 0

theorem kwg_indexedEvenPolynomial_eq_sum (ends : E -> Sym2 V)
    (x : E -> ℂ) :
    kwg_indexedEvenPolynomial ends x =
      ∑ F : KWGIndexedEvenSet ends, ∏ e ∈ F.1, x e := by
  unfold kwg_indexedEvenPolynomial
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    (Finset.univ.filter (kwg_IsEven ends))
    (fun F => by simp [KWGIndexedEvenSet])
    (fun F => ∏ e ∈ F, x e)



theorem kwg_subdiv_evenPolynomial_eq (ends : E -> Sym2 V) (x : E -> ℂ) :
    kwEvenPolynomial (kwg_subdivGraph ends) (kwg_subdivWeight (V := V) x) =
      kwg_indexedEvenPolynomial ends x := by
  rw [kwEvenPolynomial_eq_sum_actual,
    kwg_indexedEvenPolynomial_eq_sum]
  symm
  apply Fintype.sum_equiv (kwg_subdivEvenEquiv ends)
  intro F
  exact (kwg_subdivLift_weight_product ends x F.1).symm



theorem kwg_subdiv_kacWard_det
    (ends : E -> Sym2 V)
    (embedding : KWStraightLineEmbedding (kwg_subdivGraph ends))
    (x : E -> ℂ) :
    (1 - kwGraphTransition (kwg_subdivGraph ends)
      (kwg_subdivWeight (V := V) x) embedding.turnPhase).det =
        (kwg_indexedEvenPolynomial ends x) ^ 2 := by
  rw [kacWard_straightLine_arbitrary_adaptive,
    kwg_subdiv_evenPolynomial_eq]



theorem ofReal_kwg_lowTempDualSum_eq_indexedEvenPolynomial
    (P : PlanarZ2Subgraph) (beta : Real) :
    (kwg_lowTempDualSum P beta : ℂ) =
      kwg_indexedEvenPolynomial (kwg_dualEnds P)
        (fun _ => (Real.exp (-2 * beta) : ℂ)) := by
  unfold kwg_lowTempDualSum kwg_indexedEvenPolynomial
  push_cast
  apply Finset.sum_congr rfl
  intro F _
  by_cases hF : kwg_IsEven (kwg_dualEnds P) F <;> simp [hF]



theorem kwg_lowTempDualSum_sq_eq_kacWard_det
    (P : PlanarZ2Subgraph) (beta : Real)
    (embedding : KWStraightLineEmbedding
      (kwg_subdivGraph (kwg_dualEnds P))) :
    ((kwg_lowTempDualSum P beta : ℂ) ^ 2) =
      (1 - kwGraphTransition (kwg_subdivGraph (kwg_dualEnds P))
        (kwg_subdivWeight (V := kwg_Face P)
          (fun _ => (Real.exp (-2 * beta) : ℂ)))
        embedding.turnPhase).det := by
  rw [ofReal_kwg_lowTempDualSum_eq_indexedEvenPolynomial]
  exact (kwg_subdiv_kacWard_det (kwg_dualEnds P) embedding _).symm



def kwg_pathEdgeSign (P : PlanarZ2Subgraph) {u v : P.V}
    (path : P.G.Walk u v) (e : kwg_Edge P) : ℂ :=
  (-1 : ℂ) ^ (kwg_pathEdgeIndices P path).countP
    (fun a => decide (a = e))

private theorem kwg_sum_countEq_eq_countP {A : Type*} [DecidableEq A]
    (F : Finset A) (l : List A) :
    (∑ e ∈ F, l.countP (fun a => decide (a = e))) =
      l.countP (fun a => decide (a ∈ F)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.countP_cons]
      simp_rw [List.countP_cons]
      rw [Finset.sum_add_distrib, ih]
      by_cases ha : a ∈ F <;> simp [ha]


theorem ofReal_kwg_pathDefectSign_eq_prod_pathEdgeSign
    (P : PlanarZ2Subgraph) {u v : P.V} (path : P.G.Walk u v)
    (F : Finset (kwg_Edge P)) :
    (kwg_pathDefectSign P path F : ℂ) =
      ∏ e ∈ F, kwg_pathEdgeSign P path e := by
  unfold kwg_pathDefectSign kwg_pathDefectCount kwg_pathEdgeSign
  calc
    ((if Even ((kwg_pathEdgeIndices P path).countP
        fun edge => decide (edge ∈ F)) then (1 : Real) else -1 : Real) : ℂ) =
        (if Even ((kwg_pathEdgeIndices P path).countP
          fun edge => decide (edge ∈ F)) then (1 : ℂ) else -1) := by
      split_ifs <;> norm_num
    _ = (-1 : ℂ) ^ ((kwg_pathEdgeIndices P path).countP
          fun edge => decide (edge ∈ F)) := neg_one_pow_eq_ite.symm
    _ = (-1 : ℂ) ^
        (∑ e ∈ F, (kwg_pathEdgeIndices P path).countP
          (fun a => decide (a = e))) := by
      congr 1
      exact (kwg_sum_countEq_eq_countP F
        (kwg_pathEdgeIndices P path)).symm
    _ = ∏ e ∈ F,
        (-1 : ℂ) ^ (kwg_pathEdgeIndices P path).countP
          (fun a => decide (a = e)) := by
      rw [Finset.prod_pow_eq_pow_sum]



theorem ofReal_kwg_lowTempPathDualSum_eq_indexedEvenPolynomial
    (P : PlanarZ2Subgraph) (beta : Real)
    {u v : P.V} (path : P.G.Walk u v) :
    (kwg_lowTempPathDualSum P beta path : ℂ) =
      kwg_indexedEvenPolynomial (kwg_dualEnds P)
        (fun e => kwg_pathEdgeSign P path e *
          (Real.exp (-2 * beta) : ℂ)) := by
  unfold kwg_lowTempPathDualSum kwg_indexedEvenPolynomial
  push_cast
  apply Finset.sum_congr rfl
  intro F _
  by_cases hF : kwg_IsEven (kwg_dualEnds P) F
  · simp only [hF, if_true]
    rw [Finset.prod_mul_distrib,
      ← ofReal_kwg_pathDefectSign_eq_prod_pathEdgeSign]
    simp
  · simp [hF]



theorem kwg_lowTempPathDualSum_sq_eq_kacWard_det
    (P : PlanarZ2Subgraph) (beta : Real)
    {u v : P.V} (path : P.G.Walk u v)
    (embedding : KWStraightLineEmbedding
      (kwg_subdivGraph (kwg_dualEnds P))) :
    ((kwg_lowTempPathDualSum P beta path : ℂ) ^ 2) =
      (1 - kwGraphTransition (kwg_subdivGraph (kwg_dualEnds P))
        (kwg_subdivWeight (V := kwg_Face P)
          (fun e => kwg_pathEdgeSign P path e *
            (Real.exp (-2 * beta) : ℂ)))
        embedding.turnPhase).det := by
  rw [ofReal_kwg_lowTempPathDualSum_eq_indexedEvenPolynomial]
  exact (kwg_subdiv_kacWard_det (kwg_dualEnds P) embedding _).symm

end

end StatMech.Onsager
