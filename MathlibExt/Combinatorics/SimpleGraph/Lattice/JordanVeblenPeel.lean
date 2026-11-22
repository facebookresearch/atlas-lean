/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.FaithfulEvenPeel

/-!
# Peeling even-degree subgraphs via Veblen steps

A nonempty finite graph with all degrees even is not acyclic, so it has a non-bridge edge and cycle
rank at least one. The peeling step `jcx_EvenPeel` splits into a Veblen step (an even-degree
subgraph with fewer edges and face count one less exists) and a region step (each such step removes
one face-region component). Both steps hold for the unit square.

## Main definitions

* `StatMech.Lattice.jvp_VeblenStep P`: every nonempty even-degree subgraph of `P` contains a smaller
  even-degree subgraph with face count one less.
* `StatMech.Lattice.jvp_RegionStep P`: each such step lowers the number of face-region components by
  one.

## Main results

* `StatMech.Lattice.jvp_not_isAcyclic_of_even_nonempty`: a nonempty finite graph with all degrees
  even has a cycle.
* `StatMech.Lattice.jvp_exists_nonbridge_edge_of_even_nonempty`: such a graph has a non-bridge edge.
* `StatMech.Lattice.jvp_evenPeel_of_steps`: the Veblen and region steps give `jcx_EvenPeel`.
* `StatMech.Lattice.jvp_veblenStep_unitSquare`, `StatMech.Lattice.jvp_regionStep_unitSquare`: the
  steps for the unit square.
-/

@[expose] public section

open SimpleGraph Set

namespace StatMech

namespace Lattice

theorem jvp_not_isAcyclic_of_even_nonempty {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ v, Even (G.degree v)) (hne : G.edgeSet.Nonempty) : ¬ G.IsAcyclic := by
  classical
  intro hacyc
  obtain ⟨e, he⟩ := hne
  obtain ⟨a, b⟩ := e
  have hadj : G.Adj a b := by rwa [SimpleGraph.mem_edgeSet] at he
  set C := G.connectedComponentMk a with hC
  set s : Set V := (C.supp : Set V) with hs
  have : Fintype ↥s := Fintype.ofFinite _
  have : DecidableRel (G.induce s).Adj := Classical.decRel _
  have has : a ∈ s := by rw [hs, SimpleGraph.ConnectedComponent.mem_supp_iff, hC]
  have hbs : b ∈ s := by
    rw [hs, SimpleGraph.ConnectedComponent.mem_supp_iff, hC, SimpleGraph.ConnectedComponent.eq]
    exact hadj.symm.reachable
  have hGs_conn : (G.induce s).Connected := C.connected_toSimpleGraph
  have hGs_acyc : (G.induce s).IsAcyclic := hacyc.induce _
  have hGs_tree : (G.induce s).IsTree := ⟨hGs_conn, hGs_acyc⟩
  have : Nontrivial ↥s :=
    ⟨⟨⟨a, has⟩, ⟨b, hbs⟩, fun h => G.ne_of_adj hadj (Subtype.ext_iff.mp h)⟩⟩
  obtain ⟨v, hv⟩ := hGs_tree.exists_vert_degree_one_of_nontrivial
  have hsub : G.neighborSet ↑v ⊆ s := jeb_neighborSet_subset_component G C v
  have hdeg : (G.induce s).degree v = G.degree ↑v := jeb_degree_induce_eq' G s v hsub
  have hone : G.degree ↑v = 1 := hdeg ▸ hv
  exact (Nat.not_odd_iff_even.mpr (heven ↑v)) (hone ▸ ⟨0, rfl⟩)

theorem jvp_exists_nonbridge_edge_of_even_nonempty {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ v, Even (G.degree v)) (hne : G.edgeSet.Nonempty) :
    ∃ a b : V, G.Adj a b ∧ (G.deleteEdges {s(a, b)}).Reachable a b := by
  classical
  have hnacyc := jvp_not_isAcyclic_of_even_nonempty G heven hne
  rw [isAcyclic_iff_forall_isBridge] at hnacyc
  push Not at hnacyc
  obtain ⟨e, he, hnb⟩ := hnacyc
  obtain ⟨a, b⟩ := e
  have hadj : G.Adj a b := by rwa [SimpleGraph.mem_edgeSet] at he
  refine ⟨a, b, hadj, ?_⟩
  by_contra hnr
  exact hnb (SimpleGraph.isBridge_iff.mpr hnr)

theorem jvp_one_le_nullity_of_even_nonempty {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ v, Even (G.degree v)) (hne : G.edgeSet.Nonempty) : 1 ≤ nullity G := by
  classical
  obtain ⟨a, b, hadj, hr⟩ := jvp_exists_nonbridge_edge_of_even_nonempty G heven hne
  have hab : s(a, b) ∈ G.edgeSet := by rwa [SimpleGraph.mem_edgeSet]
  set G' := G.deleteEdges {s(a, b)} with hG'
  have hGeq : G = G' ⊔ edge a b := deleteEdges_sup_edge_eq G a b hab
  have hne_ab : a ≠ b := G.ne_of_adj hadj
  have hadj' : ¬ G'.Adj a b := by simp [hG', deleteEdges_adj]
  have hface : faceCount G = faceCount G' + 1 := by
    rw [hGeq]; exact faceCount_sup_edge_of_reachable G' hne_ab hadj' hr
  unfold faceCount at hface
  omega

theorem jvp_abstract_even_of_closedContour (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKle : K ≤ P.G)
    (hcc : jce_ClosedContour (jei_pushGraph P K).edgeSet) :
    ∀ v : P.V, Even (Nat.card (K.neighborSet v)) := by
  classical
  have : Fintype P.V := Fintype.ofFinite _
  have : ∀ v : P.V, Fintype (K.neighborSet v) := fun v => Fintype.ofFinite _
  have hlf : SimpleGraph.LocallyFinite (jei_pushGraph P K) :=
    jfc_pushGraph_locallyFinite P K hKle
  have hsub : jei_pushGraph P K ≤ hypercubicLattice 2 :=
    jfc_pushGraph_le_lattice P K hKle
  intro v
  have hncard : Nat.card (K.neighborSet v) = K.degree v :=
    (Nat.card_eq_fintype_card).trans (SimpleGraph.card_neighborSet_eq_degree K v)
  rw [hncard]
  have hcorner := hcc (P.emb v)
  rw [jeb_jce_degree_eq_degree (jei_pushGraph P K) hsub (P.emb v)] at hcorner
  have hdt : (jei_pushGraph P K).degree (P.emb v) = K.degree v :=
    jcx_pushGraph_degree_corner P K v
  rw [hdt] at hcorner
  exact hcorner

/-- Every nonempty subgraph `K` of `P` with even-degree image contains an even-degree subgraph
with fewer edges and face count one less. -/
def jvp_VeblenStep (P : PlanarZ2Subgraph) : Prop :=
  ∀ (K : SimpleGraph P.V), K ≤ P.G → jce_ClosedContour (jei_pushGraph P K).edgeSet → K ≠ ⊥ →
    ∃ K' : SimpleGraph P.V, K' ≤ K ∧ jce_ClosedContour (jei_pushGraph P K').edgeSet ∧
      K'.edgeSet.ncard < K.edgeSet.ncard ∧ faceCount K' + 1 = faceCount K

/-- Whenever `K' ≤ K` are even-degree subgraphs of `P` with fewer edges and face count one less,
the face-region graph of `K` has one more component than that of `K'`. -/
def jvp_RegionStep (P : PlanarZ2Subgraph) : Prop :=
  ∀ (K K' : SimpleGraph P.V), K ≤ P.G → K' ≤ K →
    jce_ClosedContour (jei_pushGraph P K).edgeSet →
    jce_ClosedContour (jei_pushGraph P K').edgeSet →
    K'.edgeSet.ncard < K.edgeSet.ncard → faceCount K' + 1 = faceCount K →
    Nat.card (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent
      = Nat.card (whb_faceRegion (jei_pushGraph P K')).ConnectedComponent + 1

theorem jvp_evenPeel_of_steps (P : PlanarZ2Subgraph)
    (hveb : jvp_VeblenStep P) (hreg : jvp_RegionStep P) : jcx_EvenPeel P := by
  intro K hKle hcc hKne
  obtain ⟨K', hK'leK, hcc', hlt, hface⟩ := hveb K hKle hcc hKne
  exact ⟨K', hK'leK.trans hKle, hcc', hlt, hface, hreg K K' hKle hK'leK hcc hcc' hlt hface⟩

theorem jvp_faithfulCountResidue_of_steps
    (h : ∀ (P : PlanarZ2Subgraph), jeb_EvenDegreeSubgraph P →
      jvp_VeblenStep P ∧ jvp_RegionStep P) :
    jeb_FaithfulCountResidue :=
  jcx_faithfulCountResidue_of_evenPeel
    (fun P hP => jvp_evenPeel_of_steps P (h P hP).1 (h P hP).2)

theorem jvp_veblenStep_unitSquare : jvp_VeblenStep jbc_Pce := by
  classical
  intro K hKle hcc hKne
  have hdec : DecidableRel K.Adj := Classical.decRel _
  have heven : ∀ i : Fin 4, Even (Nat.card (K.neighborSet i)) :=
    jvp_abstract_even_of_closedContour jbc_Pce K hKle hcc
  rcases jcx_square_even_subgraph K hKle heven with hbot | hfull
  · exact absurd hbot hKne
  · subst hfull
    obtain ⟨_, _, hlt, hface, _⟩ := jcx_square_peel_witness
    refine ⟨⊥, bot_le, ?_, hlt, hface⟩
    rw [jei_pushGraph_bot jbc_Pce, SimpleGraph.edgeSet_bot]
    have h := jce_empty_closedContour
    rwa [Finset.coe_empty] at h

theorem jvp_regionStep_unitSquare : jvp_RegionStep jbc_Pce := by
  classical
  intro K K' hKle hK'leK hcc hcc' hlt hface
  have hdecK : DecidableRel K.Adj := Classical.decRel _
  have hdecK' : DecidableRel K'.Adj := Classical.decRel _
  have hK'le : K' ≤ jbc_Pce.G := hK'leK.trans hKle
  have hKne : K ≠ ⊥ := by
    intro hb; rw [hb, SimpleGraph.edgeSet_bot, Set.ncard_empty] at hlt; omega
  have hevenK : ∀ i : Fin 4, Even (Nat.card (K.neighborSet i)) :=
    jvp_abstract_even_of_closedContour jbc_Pce K hKle hcc
  have hevenK' : ∀ i : Fin 4, Even (Nat.card (K'.neighborSet i)) :=
    jvp_abstract_even_of_closedContour jbc_Pce K' hK'le hcc'
  rcases jcx_square_even_subgraph K hKle hevenK with hKbot | hKfull
  · exact absurd hKbot hKne
  · subst hKfull
    rcases jcx_square_even_subgraph K' hK'le hevenK' with hK'bot | hK'full
    · subst hK'bot
      obtain ⟨_, _, _, _, hdual⟩ := jcx_square_peel_witness
      exact hdual
    · exfalso; rw [hK'full] at hlt; omega

theorem jvp_faceCount_deleteEdges_nonbridge {V : Type*} [Finite V]
    (G : SimpleGraph V) {a b : V} (hab : G.Adj a b)
    (hr : (G.deleteEdges {s(a, b)}).Reachable a b) :
    faceCount (G.deleteEdges {s(a, b)}) + 1 = faceCount G := by
  classical
  have hmem : s(a, b) ∈ G.edgeSet := by rwa [SimpleGraph.mem_edgeSet]
  set G' := G.deleteEdges {s(a, b)} with hG'
  have hGeq : G = G' ⊔ edge a b := deleteEdges_sup_edge_eq G a b hmem
  have hne_ab : a ≠ b := G.ne_of_adj hab
  have hadj' : ¬ G'.Adj a b := by simp [hG', deleteEdges_adj]
  have hface : faceCount G = faceCount G' + 1 := by
    rw [hGeq]; exact faceCount_sup_edge_of_reachable G' hne_ab hadj' hr
  omega

theorem jvp_summary :
    (∀ (P : PlanarZ2Subgraph), jvp_VeblenStep P → jvp_RegionStep P → jcx_EvenPeel P) ∧
      (jvp_VeblenStep jbc_Pce ∧ jvp_RegionStep jbc_Pce) ∧
      whc_FaithfulDiscreteJordan jbc_Pce :=
  ⟨fun P => jvp_evenPeel_of_steps P,
    ⟨jvp_veblenStep_unitSquare, jvp_regionStep_unitSquare⟩,
    jfc_faithfulDiscreteJordan_unitSquare⟩

end Lattice

end StatMech
