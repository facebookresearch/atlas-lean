/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































































import Mathlib
import Code.Lattice.EulerFaces2
import Code.Lattice.EulerGeneral
import Code.Lattice.JordanCycleSpace

open SimpleGraph



set_option linter.unusedSectionVars false

namespace StatMech

namespace Lattice

variable {V : Type*}











noncomputable def jes_boundedRegionCount [Finite V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  nullity G




theorem jes_faceCount_eq_boundedRegionCount_add_one [Finite V] [DecidableEq V]
    (G : SimpleGraph V) :
    faceCount G = jes_boundedRegionCount G + 1 := rfl




theorem jes_tree_boundedRegionCount_zero [Finite V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) :
    jes_boundedRegionCount G = 0 :=
  nullity_eq_zero_of_isAcyclic hG









theorem jes_closing_edge_boundedRegionCount [Finite V] [DecidableEq V] (G : SimpleGraph V)
    {a b : V} (hne : a ≠ b) (hadj : ¬ G.Adj a b) (hr : G.Reachable a b) :
    jes_boundedRegionCount (G ⊔ edge a b) = jes_boundedRegionCount G + 1 := by
  have h := faceCount_sup_edge_of_reachable G hne hadj hr
  unfold jes_boundedRegionCount faceCount at *
  omega




theorem jes_closing_edge_one_boundedRegion [Finite V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) {a b : V} (hne : a ≠ b) (hadj : ¬ G.Adj a b) (hr : G.Reachable a b) :
    jes_boundedRegionCount (G ⊔ edge a b) = 1 := by
  rw [jes_closing_edge_boundedRegionCount G hne hadj hr, jes_tree_boundedRegionCount_zero hG]





theorem jes_closing_edge_faceCount_two [Finite V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) {a b : V} (hne : a ≠ b) (hadj : ¬ G.Adj a b) (hr : G.Reachable a b) :
    faceCount (G ⊔ edge a b) = 2 := by
  rw [faceCount_sup_edge_of_reachable G hne hadj hr, faceCount_eq_one_of_isAcyclic hG]







variable [Finite V] [DecidableEq V]






theorem jes_connected_nullity_zero_isTree {G : SimpleGraph V} (hconn : G.Connected)
    (hnull : nullity G = 0) : G.IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  have hbound := card_le_edgeSet_add_components G
  rw [card_components_eq_one_of_connected hconn] at hbound
  unfold nullity at hnull
  rw [card_components_eq_one_of_connected hconn] at hnull
  rw [Nat.card_coe_set_eq]
  omega





theorem jes_exists_closing_edge_of_nullity_one {G : SimpleGraph V} (hnull : nullity G = 1) :
    ∃ a b : V, s(a, b) ∈ G.edgeSet ∧ (G.deleteEdges {s(a, b)}).Reachable a b := by
  by_contra h
  push Not at h
  have hacyc : G.IsAcyclic := by
    rw [isAcyclic_iff_forall_adj_isBridge]
    intro a b hab
    rw [isBridge_iff]
    exact ⟨hab, h a b (by rwa [SimpleGraph.mem_edgeSet])⟩
  rw [nullity_eq_zero_of_isAcyclic hacyc] at hnull
  exact one_ne_zero hnull.symm










theorem jes_delete_closing_edge_isTree {G : SimpleGraph V} (hconn : G.Connected)
    (hnull : nullity G = 1) {a b : V} (he : s(a, b) ∈ G.edgeSet)
    (hr : (G.deleteEdges {s(a, b)}).Reachable a b) :
    (G.deleteEdges {s(a, b)}).IsTree := by
  have hbridge : ¬ G.IsBridge s(a, b) := by
    rw [isBridge_iff_not_reachable_deleteEdges G he]; push Not; exact hr
  have hconn' : (G.deleteEdges {s(a, b)}).Connected :=
    hconn.connected_delete_edge_of_not_isBridge hbridge
  refine jes_connected_nullity_zero_isTree hconn' ?_
  obtain ⟨hface, _⟩ := faceCount_deleteEdges_of_not_isBridge G he hr
  unfold faceCount at hface
  unfold nullity at *
  omega




theorem jes_nullity_one_boundedRegionCount_one {G : SimpleGraph V} (hnull : nullity G = 1) :
    jes_boundedRegionCount G = 1 := hnull









theorem jes_path_edge_ncard {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    p.edgeSet.ncard = p.length := by
  classical
  have hset : p.edgeSet = (↑p.edges.toFinset : Set (Sym2 V)) := by ext e; simp [Walk.edgeSet]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hp.edges_nodup, Walk.length_edges]






theorem jes_path_coe_isTree {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    p.toSubgraph.coe.IsTree := by
  classical
  haveI : Finite ↑p.toSubgraph.verts := jcs_verts_finite p
  rw [isTree_iff_connected_and_card]
  refine ⟨Subgraph.connected_iff'.mp p.toSubgraph_connected, ?_⟩
  have hvcard : Nat.card ↑p.toSubgraph.verts = p.length + 1 := by
    rw [p.verts_toSubgraph,
      show {x | x ∈ p.support} = (↑p.support.toFinset : Set V) by ext x; simp,
      Nat.card_coe_set_eq, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support]
  have hecard : Nat.card p.toSubgraph.coe.edgeSet = p.length := by
    rw [jcs_coe_edge_card p.toSubgraph, p.edgeSet_toSubgraph, Nat.card_coe_set_eq,
      jes_path_edge_ncard p hp]
  rw [hecard, hvcard]


theorem jes_path_coe_acyclic {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    p.toSubgraph.coe.IsAcyclic :=
  (jes_path_coe_isTree p hp).isAcyclic


theorem jes_path_coe_nullity_zero {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) :
    nullity p.toSubgraph.coe = 0 :=
  nullity_eq_zero_of_isAcyclic (jes_path_coe_acyclic p hp)



theorem jes_path_coe_boundedRegionCount_zero {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) :
    jes_boundedRegionCount p.toSubgraph.coe = 0 :=
  jes_path_coe_nullity_zero p hp


theorem jes_path_coe_faceCount_one {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) :
    faceCount p.toSubgraph.coe = 1 := by
  unfold faceCount; rw [jes_path_coe_nullity_zero p hp]










instance jes_cycle_coe_isFinite {G : SimpleGraph V} {w : V} (c : G.Walk w w) :
    Finite ↑c.toSubgraph.verts :=
  jcs_verts_finite c



theorem jes_cycle_coe_connected {G : SimpleGraph V} {w : V} (c : G.Walk w w) :
    c.toSubgraph.coe.Connected :=
  Subgraph.connected_iff'.mp c.toSubgraph_connected




theorem jes_cycle_coe_nullity_one {G : SimpleGraph V} {w : V} (c : G.Walk w w)
    (hc : c.IsCycle) :
    nullity c.toSubgraph.coe = 1 :=
  jcs_cycle_nullity_eq_one c hc





theorem jes_cycle_delete_edge_isTree {G : SimpleGraph V} {w : V} (c : G.Walk w w)
    (hc : c.IsCycle) :
    ∃ (a b : ↑c.toSubgraph.verts),
      s(a, b) ∈ c.toSubgraph.coe.edgeSet ∧
      (c.toSubgraph.coe.deleteEdges {s(a, b)}).Reachable a b ∧
      (c.toSubgraph.coe.deleteEdges {s(a, b)}).IsTree ∧
      c.toSubgraph.coe = (c.toSubgraph.coe.deleteEdges {s(a, b)}) ⊔ edge a b := by
  classical
  obtain ⟨a, b, he, hr⟩ :=
    jes_exists_closing_edge_of_nullity_one (jes_cycle_coe_nullity_one c hc)
  exact ⟨a, b, he, hr, jes_delete_closing_edge_isTree (jes_cycle_coe_connected c)
      (jes_cycle_coe_nullity_one c hc) he hr,
    deleteEdges_sup_edge_eq c.toSubgraph.coe a b he⟩











theorem jes_cycle_boundedRegionCount_one {G : SimpleGraph V} {w : V} (c : G.Walk w w)
    (hc : c.IsCycle) :
    jes_boundedRegionCount c.toSubgraph.coe = 1 :=
  jes_nullity_one_boundedRegionCount_one (jes_cycle_coe_nullity_one c hc)




theorem jes_cycle_faceCount_two {G : SimpleGraph V} {w : V} (c : G.Walk w w)
    (hc : c.IsCycle) :
    faceCount c.toSubgraph.coe = 2 := by
  rw [jes_faceCount_eq_boundedRegionCount_add_one, jes_cycle_boundedRegionCount_one c hc]














theorem jes_cycle_is_tree_plus_closing_edge {G : SimpleGraph V} {w : V} (c : G.Walk w w)
    (hc : c.IsCycle) :
    ∃ (a b : ↑c.toSubgraph.verts),
      (c.toSubgraph.coe.deleteEdges {s(a, b)}).IsTree ∧
      c.toSubgraph.coe = (c.toSubgraph.coe.deleteEdges {s(a, b)}) ⊔ edge a b ∧
      jes_boundedRegionCount (c.toSubgraph.coe.deleteEdges {s(a, b)}) = 0 ∧
      jes_boundedRegionCount c.toSubgraph.coe = 1 := by
  obtain ⟨a, b, _, _, htree, heq⟩ := jes_cycle_delete_edge_isTree c hc
  exact ⟨a, b, htree, heq,
    jes_tree_boundedRegionCount_zero htree.isAcyclic,
    jes_cycle_boundedRegionCount_one c hc⟩


































end Lattice

end StatMech
