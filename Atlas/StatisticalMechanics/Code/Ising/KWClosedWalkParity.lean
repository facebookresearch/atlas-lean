/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































































import Mathlib
import Code.Ising.KramersWannierEvenToCut
import Code.Lattice.CrossingParity
import Code.Lattice.PeierlsContourFinal

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech

namespace Ising








section Coboundary

variable {V : Type*} [DecidableEq V] {Gp : SimpleGraph V}






theorem walkParity_eq_xor_of_isCoboundary {δ : Finset (Sym2 V)} (c : V → Bool)
    (hδ : ∀ {u v : V}, Gp.Adj u v → (s(u, v) ∈ δ ↔ c u ≠ c v))
    {x y : V} (p : Gp.Walk x y) :
    walkParity Gp δ p = (c x).xor (c y) := by
  induction p with
  | nil => simp
  | @cons u v w h q ih =>
    rw [walkParity_cons, ih]
    
    have hedge : decide (s(u, v) ∈ δ) = (c u).xor (c v) := by
      have : decide (s(u, v) ∈ δ) = decide (c u ≠ c v) := decide_eq_decide.mpr (hδ h)
      rw [this]
      cases c u <;> cases c v <;> simp
    rw [hedge]
    
    cases c u <;> cases c v <;> cases c w <;> rfl

end Coboundary







section ForwardHandshake

variable {V : Type*} [DecidableEq V] {Gp : SimpleGraph V}





theorem evenOnCycles_of_isCoboundary [Fintype V] [DecidableRel Gp.Adj]
    {δ : Finset (Sym2 V)} (c : V → Bool)
    (hδ : ∀ {u v : V}, Gp.Adj u v → (s(u, v) ∈ δ ↔ c u ≠ c v)) :
    EvenOnCycles Gp δ := by
  intro x p
  rw [walkParity_eq_xor_of_isCoboundary c hδ p]
  cases c x <;> rfl

omit [DecidableEq V] in



theorem cutEdges_isCoboundary [Fintype V] [DecidableRel Gp.Adj] (s : ConfigSpace V)
    {u v : V} (h : Gp.Adj u v) : s(u, v) ∈ cutEdges Gp s ↔ s u ≠ s v :=
  mem_cutEdges_iff Gp s h





theorem evenOnCycles_cutEdges [Fintype V] [DecidableRel Gp.Adj] (s : ConfigSpace V) :
    EvenOnCycles Gp (cutEdges Gp s) :=
  evenOnCycles_of_isCoboundary s (fun h => cutEdges_isCoboundary s h)


theorem evenOnCycles_of_mem_cutSpace [Fintype V] [DecidableRel Gp.Adj]
    {δ : Finset (Sym2 V)} (hδ : δ ∈ cutSpace Gp) : EvenOnCycles Gp δ := by
  rw [cutSpace, Finset.mem_image] at hδ
  obtain ⟨s, _, rfl⟩ := hδ
  exact evenOnCycles_cutEdges s

end ForwardHandshake









section Equivalence

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp : SimpleGraph V} [DecidableRel Gp.Adj]





theorem evenOnCycles_iff_mem_cutSpace [Nonempty V] (hG : Gp.Preconnected)
    {δ : Finset (Sym2 V)} (hδsub : δ ⊆ Gp.edgeFinset) :
    EvenOnCycles Gp δ ↔ δ ∈ cutSpace Gp :=
  ⟨fun hev => mem_cutSpace_of_evenOnCycles hG hδsub hev, evenOnCycles_of_mem_cutSpace⟩



theorem isCoboundary_iff_mem_cutSpace [Nonempty V] (hG : Gp.Preconnected)
    {δ : Finset (Sym2 V)} (hδsub : δ ⊆ Gp.edgeFinset) :
    (∃ c : V → Bool, ∀ {u v : V}, Gp.Adj u v → (s(u, v) ∈ δ ↔ c u ≠ c v))
      ↔ δ ∈ cutSpace Gp := by
  constructor
  · rintro ⟨c, hc⟩
    exact (evenOnCycles_iff_mem_cutSpace hG hδsub).mp (evenOnCycles_of_isCoboundary c hc)
  · intro hδ
    rw [cutSpace, Finset.mem_image] at hδ
    obtain ⟨s, _, rfl⟩ := hδ
    exact ⟨s, fun h => cutEdges_isCoboundary s h⟩

end Equivalence
















section SideColouring

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]











def DualWalkHasSideColouring (Gp Gd : SimpleGraph V) [DecidableRel Gp.Adj]
    (ψ : Sym2 V ≃ Sym2 V) : Prop :=
  ∀ {w : V} (W : Gd.Walk w w), ∃ c : V → Bool,
    ∀ {u v : V}, Gp.Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image ψ.symm ↔ c u ≠ c v)

omit [DecidableRel Gd.Adj] in





theorem closedDualWalkParity_of_sideColouring
    (ψ : Sym2 V ≃ Sym2 V) (hside : DualWalkHasSideColouring Gp Gd ψ) :
    ClosedDualWalkParity Gp Gd ψ := by
  intro w W
  obtain ⟨c, hc⟩ := hside W
  exact evenOnCycles_of_isCoboundary c (fun h => hc h)







theorem even_to_cut_of_sideColouring [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hdecomp : EvenSubgraphWalkDecomp Gd)
    (hside : DualWalkHasSideColouring Gp Gd ψ) :
    ∀ F ∈ evenSubgraphs Gd, (F.image ψ.symm) ∈ cutSpace Gp :=
  even_to_cut_of_closedWalkParity hG ψ hsymm hdecomp
    (closedDualWalkParity_of_sideColouring ψ hside)












noncomputable def edgeCrossing_of_sideColouring [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hedge : ∀ e ∈ Gp.edgeFinset, ψ e ∈ Gd.edgeFinset)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hfwd : ∀ δ ∈ cutSpace Gp, IsEvenSubgraph (δ.image ψ))
    (hdecomp : EvenSubgraphWalkDecomp Gd)
    (hside : DualWalkHasSideColouring Gp Gd ψ) :
    EdgeCrossing Gp Gd where
  ψ := ψ
  edge_mem := hedge
  cut_to_even := hfwd
  even_to_cut := even_to_cut_of_sideColouring hG ψ hsymm hdecomp hside









omit [Fintype V] [DecidableRel Gd.Adj] in




theorem dualWalkHasSideColouring_of_edgeless (ψ : Sym2 V ≃ Sym2 V) (hGd : Gd.edgeSet = ∅) :
    DualWalkHasSideColouring Gp Gd ψ := by
  intro w W
  refine ⟨fun _ => false, ?_⟩
  intro u v _
  have hnil : W.edges = [] := edges_eq_nil_of_isEmpty_edgeSet hGd W
  have hempty : (W.edges.toFinset).image ψ.symm = (∅ : Finset (Sym2 V)) := by
    rw [hnil]; simp
  rw [hempty]
  simp

end SideColouring























section EvenSubgraphDecomp

variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

def subgraphF (F : Finset (Sym2 V)) : SimpleGraph V := SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))

theorem subgraphF_adj (F : Finset (Sym2 V)) (a b : V) :
    (subgraphF F).Adj a b ↔ s(a,b) ∈ F ∧ a ≠ b := by
  unfold subgraphF; rw [SimpleGraph.fromEdgeSet_adj]; simp

theorem mem_edgeSet_subgraphF (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag) (e : Sym2 V) :
    e ∈ (subgraphF F).edgeSet ↔ e ∈ F := by
  unfold subgraphF
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · rintro ⟨h1, _⟩; exact Finset.mem_coe.mp h1
  · intro h; exact ⟨Finset.mem_coe.mpr h, by rw [Sym2.mem_diagSet]; exact hF e h⟩

noncomputable instance subgraphF_decRel (F : Finset (Sym2 V)) : DecidableRel (subgraphF F).Adj :=
  Classical.decRel _

theorem degree_subgraphF_eq_incCount (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag) (v : V) :
    (subgraphF F).degree v = incCount F v := by
  classical
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  unfold incCount subgraphF
  apply Finset.card_bij (fun e _ => e)
  · intro e he
    rw [SimpleGraph.mem_incidenceFinset] at he
    have hmem : e ∈ (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).edgeSet ∧ v ∈ e := he
    rw [SimpleGraph.edgeSet_fromEdgeSet] at hmem
    rw [Finset.mem_filter]; exact ⟨hmem.1.1, hmem.2⟩
  · intro a _ b _ h; exact h
  · intro e he
    rw [Finset.mem_filter] at he
    refine ⟨e, ?_, rfl⟩
    rw [SimpleGraph.mem_incidenceFinset]
    have : e ∈ (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).edgeSet ∧ v ∈ e := by
      refine ⟨?_, he.2⟩
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      exact ⟨Finset.mem_coe.mpr he.1, by rw [Sym2.mem_diagSet]; exact hF e he.1⟩
    exact this

theorem subgraphF_even (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (hev : IsEvenSubgraph F) (v : V) : Even ((subgraphF F).degree v) := by
  rw [degree_subgraphF_eq_incCount F hF v]; exact hev v



def compF (F : Finset (Sym2 V)) (f : V) : SimpleGraph V where
  Adj a b := (subgraphF F).Adj a b ∧ (subgraphF F).Reachable f a ∧ (subgraphF F).Reachable f b
  symm := by rintro a b ⟨h, ha, hb⟩; exact ⟨h.symm, hb, ha⟩
  loopless := by refine ⟨fun a ⟨h, _, _⟩ => (subgraphF F).irrefl h⟩

theorem compF_le (F : Finset (Sym2 V)) (f : V) : compF F f ≤ subgraphF F := fun _ _ h => h.1

noncomputable instance compF_decRel (F : Finset (Sym2 V)) (f : V) :
    DecidableRel (compF F f).Adj := Classical.decRel _

theorem compF_neighborSet_eq (F : Finset (Sym2 V)) {f a : V}
    (ha : (subgraphF F).Reachable f a) :
    (compF F f).neighborSet a = (subgraphF F).neighborSet a := by
  ext b; simp only [SimpleGraph.mem_neighborSet]
  constructor
  · rintro ⟨h, _, _⟩; exact h
  · intro h; exact ⟨h, ha, ha.trans h.reachable⟩

theorem compF_neighborSet_empty (F : Finset (Sym2 V)) {f a : V}
    (ha : ¬ (subgraphF F).Reachable f a) :
    (compF F f).neighborSet a = ∅ := by
  ext b; simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
  rintro ⟨_, hra, _⟩; exact ha hra

theorem compF_degree_even (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (hev : IsEvenSubgraph F) (f a : V) : Even ((compF F f).degree a) := by
  classical
  by_cases ha : (subgraphF F).Reachable f a
  · rw [← SimpleGraph.card_neighborSet_eq_degree]
    have hcard : Fintype.card ((compF F f).neighborSet a) = (subgraphF F).degree a := by
      rw [← SimpleGraph.card_neighborSet_eq_degree]
      exact Fintype.card_congr (Equiv.setCongr (compF_neighborSet_eq F ha))
    rw [hcard]; exact subgraphF_even F hF hev a
  · rw [← SimpleGraph.card_neighborSet_eq_degree]
    have hempty : (compF F f).neighborSet a = ∅ := compF_neighborSet_empty F ha
    have hcard : Fintype.card ((compF F f).neighborSet a) = 0 := by
      rw [Fintype.card_eq_zero_iff]; exact ⟨fun x => (hempty ▸ x.2 : (x:V) ∈ (∅:Set V))⟩
    rw [hcard]; exact Even.zero



noncomputable def compSuppF (F : Finset (Sym2 V)) (f : V) : Finset V :=
  Finset.univ.filter (fun g => (subgraphF F).Reachable f g)

theorem mem_compSuppF (F : Finset (Sym2 V)) {f g : V} :
    g ∈ compSuppF F f ↔ (subgraphF F).Reachable f g := by
  unfold compSuppF; rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem self_mem_compSuppF (F : Finset (Sym2 V)) (f : V) : f ∈ compSuppF F f := by
  rw [mem_compSuppF]


theorem compF_support_subset (F : Finset (Sym2 V)) (f : V) :
    (compF F f).support ⊆ (compSuppF F f : Set V) := by
  intro a ha
  rw [SimpleGraph.mem_support] at ha
  obtain ⟨b, hadj, hra, _⟩ := ha
  rw [Finset.mem_coe, mem_compSuppF]; exact hra


theorem compF_edge_of_walk_from_base (F : Finset (Sym2 V)) {f g : V}
    (q : (subgraphF F).Walk f g) {e : Sym2 V} (he : e ∈ q.edges) :
    e ∈ (compF F f).edgeSet := by
  induction e with
  | h x y =>
    have hxadj : (subgraphF F).Adj x y := q.adj_of_mem_edges he
    have hx : x ∈ q.support := q.fst_mem_support_of_mem_edges he
    have hy : y ∈ q.support := q.snd_mem_support_of_mem_edges he
    have hrx : (subgraphF F).Reachable f x := ⟨q.takeUntil x hx⟩
    have hry : (subgraphF F).Reachable f y := ⟨q.takeUntil y hy⟩
    rw [SimpleGraph.mem_edgeSet]; exact ⟨hxadj, hrx, hry⟩

theorem compF_reachable_of_reachable (F : Finset (Sym2 V)) {f g : V}
    (h : (subgraphF F).Reachable f g) : (compF F f).Reachable f g := by
  obtain ⟨p⟩ := h
  exact ⟨p.transfer (compF F f) (fun e he => compF_edge_of_walk_from_base F p he)⟩

theorem compF_walk_in_compSuppF (F : Finset (Sym2 V)) {f : V} {g : V}
    (p : (compF F f).Walk f g) : ∀ v ∈ p.support, v ∈ compSuppF F f := by
  intro v hv
  rw [mem_compSuppF]
  have hmem : v ∈ (p.mapLe (compF_le F f)).support := by
    rw [SimpleGraph.Walk.support_mapLe_eq_support]; exact hv
  exact ⟨(p.mapLe (compF_le F f)).takeUntil v hmem⟩


theorem reachable_induce_of_walk_in_set' {G : SimpleGraph V} {S : Set V}
    {a b : V} (p : G.Walk a b) (hsub : ∀ v ∈ p.support, v ∈ S) (ha : a ∈ S) :
    (G.induce S).Reachable ⟨a, ha⟩ ⟨b, hsub b p.end_mem_support⟩ := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y z hxy q ih =>
    have hyS : y ∈ S := hsub y (by
      rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ q.start_mem_support)
    have hqsub : ∀ v ∈ q.support, v ∈ S := fun v hv =>
      hsub v (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hv)
    have hadjI : (G.induce S).Adj ⟨x, ha⟩ ⟨y, hyS⟩ := by rw [SimpleGraph.induce_adj]; exact hxy
    exact (SimpleGraph.Adj.reachable hadjI).trans (ih hqsub hyS)

theorem compF_induce_connected (F : Finset (Sym2 V)) (f : V) :
    ((compF F f).induce (compSuppF F f : Set V)).Connected := by
  have hself : f ∈ compSuppF F f := self_mem_compSuppF F f
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨f, hself⟩⟩⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  have ha' : a ∈ compSuppF F f := Finset.mem_coe.mp ha
  have hb' : b ∈ compSuppF F f := Finset.mem_coe.mp hb
  rw [mem_compSuppF] at ha' hb'
  obtain ⟨pa⟩ := compF_reachable_of_reachable F ha'
  obtain ⟨pb⟩ := compF_reachable_of_reachable F hb'
  have hp := pa.reverse.append pb
  have hsub : ∀ v ∈ (pa.reverse.append pb).support, v ∈ compSuppF F f := by
    intro v hv
    rw [SimpleGraph.Walk.support_append] at hv
    rcases List.mem_append.mp hv with hva | hvb
    · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hva
      exact compF_walk_in_compSuppF F pa v hva
    · exact compF_walk_in_compSuppF F pb v (List.mem_of_mem_tail hvb)
  have hrec := reachable_induce_of_walk_in_set' (pa.reverse.append pb) hsub ha
  convert hrec using 2



theorem compF_eulerCircuit (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (hev : IsEvenSubgraph F) (f : V) :
    ∃ c : (compF F f).Walk f f, ∀ e ∈ (compF F f).edgeSet, e ∈ c.edges := by
  obtain ⟨c, _htrail, hcov⟩ := StatMech.Lattice.EulerianExistence.exists_closed_eulerian_of_finite_support
    (compF F f) (compSuppF F f) (compF_support_subset F f)
    (compF_induce_connected F f) (compF_degree_even F hF hev f)
    (Finset.mem_coe.mpr (self_mem_compSuppF F f))
  exact ⟨c, hcov⟩


theorem mem_compF_edgeSet (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag) (f : V) (e : Sym2 V) :
    e ∈ (compF F f).edgeSet ↔ (e ∈ F ∧ ∀ x ∈ e, (subgraphF F).Reachable f x) := by
  induction e with
  | h x y =>
    rw [SimpleGraph.mem_edgeSet]
    constructor
    · rintro ⟨hadj, hrx, hry⟩
      rw [subgraphF_adj] at hadj
      refine ⟨hadj.1, ?_⟩
      intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact hrx
      · exact hry
    · rintro ⟨hmem, hreach⟩
      have hxr : (subgraphF F).Reachable f x := hreach x (by rw [Sym2.mem_iff]; left; rfl)
      have hyr : (subgraphF F).Reachable f y := hreach y (by rw [Sym2.mem_iff]; right; rfl)
      have hadj : (subgraphF F).Adj x y := by
        rw [subgraphF_adj]; exact ⟨hmem, by
          intro hxy; subst hxy; exact hF _ hmem (by rw [Sym2.mk_isDiag_iff])⟩
      exact ⟨hadj, hxr, hyr⟩



noncomputable def compEulerWalk (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (hev : IsEvenSubgraph F) (f : V) : (compF F f).Walk f f :=
  (compF_eulerCircuit F hF hev f).choose

theorem compEulerWalk_cov (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (hev : IsEvenSubgraph F) (f : V) :
    ∀ e ∈ (compF F f).edgeSet, e ∈ (compEulerWalk F hF hev f).edges :=
  (compF_eulerCircuit F hF hev f).choose_spec

theorem compEulerWalk_edges_toFinset (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (hev : IsEvenSubgraph F) (f : V) :
    ((compEulerWalk F hF hev f).edges.toFinset : Finset (Sym2 V))
      = F.filter (fun e => ∀ x ∈ e, (subgraphF F).Reachable f x) := by
  ext e
  rw [List.mem_toFinset, Finset.mem_filter]
  constructor
  · intro he
    have hadj : e ∈ (compF F f).edgeSet := (compEulerWalk F hF hev f).edges_subset_edgeSet he
    rw [mem_compF_edgeSet F hF f e] at hadj
    exact hadj
  · intro ⟨hmem, hreach⟩
    have : e ∈ (compF F f).edgeSet := by rw [mem_compF_edgeSet F hF f e]; exact ⟨hmem, hreach⟩
    exact compEulerWalk_cov F hF hev f e this









section ComponentIndex

variable {V : Type} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

open SimpleGraph (ConnectedComponent)



theorem edge_reachable_from_out (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    {x y : V} (hmem : s(x, y) ∈ F) :
    ∀ z ∈ s(x, y), (subgraphF F).Reachable ((subgraphF F).connectedComponentMk x).out z := by
  intro z hz
  have hadj : (subgraphF F).Adj x y := by
    rw [subgraphF_adj]; exact ⟨hmem, by intro h; subst h; exact hF _ hmem (by rw [Sym2.mk_isDiag_iff])⟩
  have hrxy : (subgraphF F).Reachable x y := hadj.reachable
  
  have hox : (subgraphF F).Reachable ((subgraphF F).connectedComponentMk x).out x := by
    have := ((subgraphF F).connectedComponentMk x).out_eq
    exact ConnectedComponent.exact this
  rw [Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · exact hox
  · exact hox.trans hrxy

theorem evenSubgraph_decomp (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (hev : IsEvenSubgraph F) :
    ∃ (ι : Type) (_ : DecidableEq ι) (s : Finset ι) (w : ι → V)
      (W : (i : ι) → (subgraphF F).Walk (w i) (w i)),
      F = s.biUnion (fun i => (W i).edges.toFinset) ∧
      (s : Set ι).PairwiseDisjoint (fun i => (W i).edges.toFinset) := by
  classical
  refine ⟨(subgraphF F).ConnectedComponent, inferInstance, Finset.univ,
    fun c => c.out,
    fun c => (compEulerWalk F hF hev c.out).mapLe (compF_le F c.out), ?_, ?_⟩
  · 
    ext e
    rw [Finset.mem_biUnion]
    constructor
    · intro he
      induction e with
      | h x y =>
        refine ⟨(subgraphF F).connectedComponentMk x, Finset.mem_univ _, ?_⟩
        simp only
        rw [SimpleGraph.Walk.edges_mapLe_eq_edges, List.mem_toFinset]
        
        have hcov := compEulerWalk_cov F hF hev ((subgraphF F).connectedComponentMk x).out
        apply hcov
        rw [mem_compF_edgeSet F hF _ s(x,y)]
        exact ⟨he, edge_reachable_from_out F hF he⟩
    · rintro ⟨c, _, hc⟩
      simp only at hc
      rw [SimpleGraph.Walk.edges_mapLe_eq_edges, List.mem_toFinset] at hc
      have : e ∈ (compF F c.out).edgeSet :=
        (compEulerWalk F hF hev c.out).edges_subset_edgeSet hc
      rw [mem_compF_edgeSet F hF c.out e] at this
      exact this.1
  · 
    intro c _ d _ hcd
    apply Finset.disjoint_left.mpr
    intro e hec hed
    simp only at hec hed
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges, List.mem_toFinset] at hec hed
    have hcc : e ∈ (compF F c.out).edgeSet :=
      (compEulerWalk F hF hev c.out).edges_subset_edgeSet hec
    have hdd : e ∈ (compF F d.out).edgeSet :=
      (compEulerWalk F hF hev d.out).edges_subset_edgeSet hed
    rw [mem_compF_edgeSet F hF c.out e] at hcc
    rw [mem_compF_edgeSet F hF d.out e] at hdd
    
    revert hcc hdd
    induction e with
    | h x y =>
      intro hcc hdd
      have hcx : (subgraphF F).Reachable c.out x := hcc.2 x (by rw [Sym2.mem_iff]; left; rfl)
      have hdx : (subgraphF F).Reachable d.out x := hdd.2 x (by rw [Sym2.mem_iff]; left; rfl)
      have : c = d := by
        have h1 : (subgraphF F).connectedComponentMk c.out
            = (subgraphF F).connectedComponentMk x := ConnectedComponent.sound hcx
        have h2 : (subgraphF F).connectedComponentMk d.out
            = (subgraphF F).connectedComponentMk x := ConnectedComponent.sound hdx
        have hco : (subgraphF F).connectedComponentMk c.out = c := c.out_eq
        have hdo : (subgraphF F).connectedComponentMk d.out = d := d.out_eq
        rw [hco] at h1; rw [hdo] at h2; rw [h1, ← h2]
      exact hcd this



theorem subgraphF_le_of_subset {Gd : SimpleGraph V} [DecidableRel Gd.Adj]
    {F : Finset (Sym2 V)} (hFsub : F ⊆ Gd.edgeFinset) : subgraphF F ≤ Gd := by
  intro a b hab
  rw [subgraphF_adj] at hab
  have : s(a,b) ∈ Gd.edgeFinset := hFsub hab.1
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
  exact this


theorem evenSubgraphs_no_diag {Gd : SimpleGraph V} [DecidableRel Gd.Adj]
    {F : Finset (Sym2 V)} (hFsub : F ⊆ Gd.edgeFinset) (e : Sym2 V) (he : e ∈ F) : ¬ e.IsDiag := by
  have : e ∈ Gd.edgeFinset := hFsub he
  rw [SimpleGraph.mem_edgeFinset] at this
  exact Gd.not_isDiag_of_mem_edgeSet this


theorem edges_mapLe_toFinset {G H : SimpleGraph V} (h : G ≤ H) {a b : V} (p : G.Walk a b) :
    (p.mapLe h).edges.toFinset = p.edges.toFinset := by
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges]


theorem evenSubgraphWalkDecomp_general (Gd : SimpleGraph V) [DecidableRel Gd.Adj] :
    EvenSubgraphWalkDecomp Gd := by
  classical
  intro F hF
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hF
  obtain ⟨hFsub, hFev⟩ := hF
  have hF_no_diag : ∀ e ∈ F, ¬ e.IsDiag := fun e he => evenSubgraphs_no_diag hFsub e he
  obtain ⟨ι, hιdec, s, w, W, hcov, hdisj⟩ := evenSubgraph_decomp F hF_no_diag hFev
  have hle : subgraphF F ≤ Gd := subgraphF_le_of_subset hFsub
  have hbu : s.biUnion (fun i => (W i).edges.toFinset)
      = s.biUnion (fun i => ((W i).mapLe hle).edges.toFinset) := by
    apply Finset.biUnion_congr rfl
    intro i _
    exact (edges_mapLe_toFinset hle (W i)).symm
  refine ⟨ι, hιdec, s, w, fun i => (W i).mapLe hle, ?_, ?_⟩
  · exact hcov.trans hbu
  · intro i hi j hj hij
    have hd := hdisj hi hj hij
    simp only [Function.onFun]
    rw [edges_mapLe_toFinset hle (W i), edges_mapLe_toFinset hle (W j)]
    exact hd

end ComponentIndex

end EvenSubgraphDecomp

















section RegionSide

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]





noncomputable def regionBoundary (Gp : SimpleGraph V) [DecidableRel Gp.Adj] (S : V → Bool) :
    Finset (Sym2 V) :=
  cutEdges Gp S

omit [DecidableEq V] in



theorem mem_regionBoundary_iff (S : V → Bool) {u v : V} (h : Gp.Adj u v) :
    s(u, v) ∈ regionBoundary Gp S ↔ S u ≠ S v :=
  cutEdges_isCoboundary S h







theorem evenOnCycles_regionBoundary (S : V → Bool) :
    EvenOnCycles Gp (regionBoundary Gp S) :=
  evenOnCycles_of_isCoboundary S (fun h => mem_regionBoundary_iff S h)











def DualWalkBoundsRegion (Gp Gd : SimpleGraph V) [DecidableRel Gp.Adj]
    (ψ : Sym2 V ≃ Sym2 V) : Prop :=
  ∀ {w : V} (W : Gd.Walk w w), ∃ S : V → Bool,
    ∀ {u v : V}, Gp.Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image ψ.symm ↔ S u ≠ S v)

omit [Fintype V] [DecidableRel Gd.Adj] in




theorem dualWalkBoundsRegion_isSideColouring
    (ψ : Sym2 V ≃ Sym2 V) (hreg : DualWalkBoundsRegion Gp Gd ψ) :
    DualWalkHasSideColouring Gp Gd ψ := by
  intro w W
  obtain ⟨S, hS⟩ := hreg W
  exact ⟨S, fun h => hS h⟩

omit [Fintype V] [DecidableRel Gd.Adj] in





theorem closedDualWalkParity_of_boundsRegion
    (ψ : Sym2 V ≃ Sym2 V) (hreg : DualWalkBoundsRegion Gp Gd ψ) :
    ClosedDualWalkParity Gp Gd ψ := by
  intro w W
  obtain ⟨S, hS⟩ := hreg W
  
  
  intro x p
  rw [walkParity_eq_xor_of_isCoboundary S (fun h => hS h) p]
  cases S x <;> rfl







theorem even_to_cut_of_boundsRegion [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hdecomp : EvenSubgraphWalkDecomp Gd)
    (hreg : DualWalkBoundsRegion Gp Gd ψ) :
    ∀ F ∈ evenSubgraphs Gd, (F.image ψ.symm) ∈ cutSpace Gp :=
  even_to_cut_of_sideColouring hG ψ hsymm hdecomp
    (dualWalkBoundsRegion_isSideColouring ψ hreg)








noncomputable def edgeCrossing_of_boundsRegion [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hedge : ∀ e ∈ Gp.edgeFinset, ψ e ∈ Gd.edgeFinset)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hfwd : ∀ δ ∈ cutSpace Gp, IsEvenSubgraph (δ.image ψ))
    (hdecomp : EvenSubgraphWalkDecomp Gd)
    (hreg : DualWalkBoundsRegion Gp Gd ψ) :
    EdgeCrossing Gp Gd where
  ψ := ψ
  edge_mem := hedge
  cut_to_even := hfwd
  even_to_cut := even_to_cut_of_boundsRegion hG ψ hsymm hdecomp hreg

omit [Fintype V] [DecidableRel Gd.Adj] in




theorem dualWalkBoundsRegion_of_edgeless (ψ : Sym2 V ≃ Sym2 V) (hGd : Gd.edgeSet = ∅) :
    DualWalkBoundsRegion Gp Gd ψ := by
  intro w W
  refine ⟨fun _ => false, ?_⟩
  intro u v _
  have hnil : W.edges = [] := edges_eq_nil_of_isEmpty_edgeSet hGd W
  have hempty : (W.edges.toFinset).image ψ.symm = (∅ : Finset (Sym2 V)) := by
    rw [hnil]; simp
  rw [hempty]
  simp

end RegionSide

























section LatticeBridge

open StatMech.Lattice




noncomputable def latticeSide (S : Set (Site 2)) : Site 2 → Bool :=
  fun x => @decide (x ∈ S) (Classical.propDecidable _)

@[simp] theorem latticeSide_eq_true {S : Set (Site 2)} {x : Site 2} :
    latticeSide S x = true ↔ x ∈ S := by
  unfold latticeSide
  exact @decide_eq_true_iff (x ∈ S) (Classical.propDecidable _)







theorem crossCount_even_iff_latticeSide (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    Even (crossCount S w) ↔ latticeSide S x = latticeSide S y := by
  rw [crossCount_parity S w]
  constructor
  · intro hiff
    by_cases hx : x ∈ S
    · rw [(latticeSide_eq_true).mpr hx, (latticeSide_eq_true).mpr (hiff.mp hx)]
    · have hy : y ∉ S := fun hy => hx (hiff.mpr hy)
      have e1 : latticeSide S x = false := by
        cases h : latticeSide S x with
        | false => rfl
        | true => exact absurd ((latticeSide_eq_true).mp h) hx
      have e2 : latticeSide S y = false := by
        cases h : latticeSide S y with
        | false => rfl
        | true => exact absurd ((latticeSide_eq_true).mp h) hy
      rw [e1, e2]
  · intro hcol
    constructor
    · intro hx
      have : latticeSide S x = true := (latticeSide_eq_true).mpr hx
      rw [hcol] at this
      exact (latticeSide_eq_true).mp this
    · intro hy
      have : latticeSide S y = true := (latticeSide_eq_true).mpr hy
      rw [← hcol] at this
      exact (latticeSide_eq_true).mp this







theorem latticeRegionBoundary_evenOnLoop (S : Set (Site 2)) {x : Site 2}
    (w : (hypercubicLattice 2).Walk x x) : Even (crossCount S w) :=
  (crossCount_even_iff_latticeSide S w).mpr rfl








theorem latticeSide_isRegion_of_pullback_eq_bdEdge
    {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj] (ψ : Sym2 (Site 2) ≃ Sym2 (Site 2))
    (S : Set (Site 2)) {w : Site 2} (W : Gd.Walk w w)
    (hpull : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image ψ.symm ↔ bdEdge S s(u, v))) :
    ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image ψ.symm ↔ latticeSide S u ≠ latticeSide S v) := by
  intro u v h
  rw [hpull h, bdEdge_mk]
  
  have hu : u ∈ S ↔ latticeSide S u = true := (latticeSide_eq_true).symm
  have hv : v ∈ S ↔ latticeSide S v = true := (latticeSide_eq_true).symm
  rw [hu, hv]
  cases latticeSide S u <;> cases latticeSide S v <;> simp

end LatticeBridge













section UnconditionalCapstone

variable {V : Type} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]






theorem even_to_cut_of_boundsRegion' [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hreg : DualWalkBoundsRegion Gp Gd ψ) :
    ∀ F ∈ evenSubgraphs Gd, (F.image ψ.symm) ∈ cutSpace Gp :=
  even_to_cut_of_boundsRegion hG ψ hsymm (evenSubgraphWalkDecomp_general Gd) hreg








noncomputable def edgeCrossing_of_boundsRegion' [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hedge : ∀ e ∈ Gp.edgeFinset, ψ e ∈ Gd.edgeFinset)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hfwd : ∀ δ ∈ cutSpace Gp, IsEvenSubgraph (δ.image ψ))
    (hreg : DualWalkBoundsRegion Gp Gd ψ) :
    EdgeCrossing Gp Gd :=
  edgeCrossing_of_boundsRegion hG ψ hedge hsymm hfwd (evenSubgraphWalkDecomp_general Gd) hreg







theorem isingZ_self_dual_of_boundsRegion [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hedge : ∀ e ∈ Gp.edgeFinset, ψ e ∈ Gd.edgeFinset)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hfwd : ∀ δ ∈ cutSpace Gp, IsEvenSubgraph (δ.image ψ))
    (hreg : DualWalkBoundsRegion Gp Gd ψ)
    (β βstar : ℝ) (htemp : Real.tanh βstar = Real.exp (-2 * β)) :
    isingZ Gd βstar 0
      = ((2 : ℝ) ^ Fintype.card V * (Real.cosh βstar) ^ Gd.edgeFinset.card
        / (Real.exp (β * Gp.edgeFinset.card) * 2)) * isingZ Gp β 0 :=
  isingZ_self_dual_of_edgeCrossing hG
    (edgeCrossing_of_boundsRegion' hG ψ hedge hsymm hfwd hreg) β βstar htemp

end UnconditionalCapstone

end Ising

end StatMech
