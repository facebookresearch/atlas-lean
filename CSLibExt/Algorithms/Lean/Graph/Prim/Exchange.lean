/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Signed-real cut exchange for Prim

Adapted from CLRS, fourth edition, section 21.2, Prim's algorithm.
Proofs and executable code authored with Codex under Adam Kiezun's authorization.
-/

open scoped BigOperators

namespace SimpleGraph

variable {n : Nat}

/-- The genuine canonical edge sum of a finite simple graph. -/
private noncomputable def totalEdgeWeight (w : Sym2 (Fin n) → ℝ)
    (G : SimpleGraph (Fin n)) : ℝ := by
  classical
  exact ∑ e ∈ G.edgeFinset, w e

/-- Deleting one present edge subtracts its unrestricted real weight. -/
private lemma totalEdgeWeight_deleteEdges_singleton (w : Sym2 (Fin n) → ℝ)
    (G : SimpleGraph (Fin n)) {e : Sym2 (Fin n)} (he : e ∈ G.edgeSet) :
    totalEdgeWeight w (G.deleteEdges {e}) = totalEdgeWeight w G - w e := by
  classical
  simp only [totalEdgeWeight, edgeFinset, edgeSet_deleteEdges, Set.toFinset_sdiff,
    Set.toFinset_singleton, Finset.sdiff_singleton_eq_erase]
  exact Finset.sum_erase_eq_sub (by simpa using he)

/-- Adding an absent non-loop edge adds exactly its unrestricted real weight. -/
private lemma totalEdgeWeight_sup_edge (w : Sym2 (Fin n) → ℝ)
    (G : SimpleGraph (Fin n)) {u v : Fin n} (huv : u ≠ v) (hnew : ¬G.Adj u v) :
    totalEdgeWeight w (G ⊔ edge u v) = totalEdgeWeight w G + w s(u, v) := by
  classical
  have hedge : (edge u v).edgeFinset = {s(u, v)} := by
    simp [edgeFinset, edgeSet_edge_of_ne huv]
  have hdis : Disjoint G.edgeFinset {s(u, v)} :=
    Finset.disjoint_singleton_right.mpr (by simpa using hnew)
  simp only [totalEdgeWeight, edgeFinset_sup, hedge, Finset.sum_union hdis,
    Finset.sum_singleton]

/-- Deleting a present edge and adding an absent non-loop edge replaces its weight. -/
private lemma totalEdgeWeight_deleteEdges_sup_edge (w : Sym2 (Fin n) → ℝ)
    (G : SimpleGraph (Fin n)) {x y u v : Fin n}
    (hxy : G.Adj x y) (huv : u ≠ v) (hnew : ¬G.Adj u v) :
    totalEdgeWeight w (G.deleteEdges {s(x, y)} ⊔ edge u v) =
      totalEdgeWeight w G - w s(x, y) + w s(u, v) := by
  classical
  have hnotDelete : ¬(G.deleteEdges {s(x, y)}).Adj u v :=
    fun h ↦ hnew h.1
  rw [totalEdgeWeight_sup_edge w _ huv hnotDelete,
    totalEdgeWeight_deleteEdges_singleton w G hxy]

/-- A cut respects `A` when no edge of `A` crosses the cut. -/
private def RespectsCut (A : SimpleGraph (Fin n)) (S : Set (Fin n)) : Prop :=
  ∀ ⦃u v⦄, A.Adj u v → (u ∈ S ↔ v ∈ S)

private lemma exists_cut_edge_on_path {T A : SimpleGraph (Fin n)} {S : Set (Fin n)}
    {u v : Fin n} (p : T.Walk u v) (hrespect : RespectsCut A S)
    (hu : u ∈ S) (hv : v ∉ S) :
    ∃ x y, T.Adj x y ∧ x ∈ S ∧ y ∉ S ∧ ¬A.Adj x y ∧ s(x, y) ∈ p.edges := by
  obtain ⟨⟨⟨x, y⟩, hxy⟩, hd, hx, hy⟩ := p.exists_boundary_dart S hu hv
  have hnotA : ¬A.Adj x y := by
    intro hA
    exact hy ((hrespect hA).mp hx)
  refine ⟨x, y, hxy, hx, hy, hnotA, ?_⟩
  simpa only [Walk.edges_eq_map_darts, Dart.edge_mk] using
    List.mem_map_of_mem (f := Dart.edge) hd

private lemma not_reachable_delete_edge_of_mem_path {T : SimpleGraph (Fin n)}
    {u v x y : Fin n} (hT : T.IsAcyclic) (p : T.Walk u v) (hp : p.IsPath)
    (he : s(x, y) ∈ p.edges) : ¬(T.deleteEdges {s(x, y)}).Reachable u v := by
  classical
  intro hreach
  obtain ⟨q, hq⟩ := hreach.exists_isPath
  let qT : T.Path u v :=
    ⟨Walk.mapLe (deleteEdges_le {s(x, y)}) q, hq.mapLe (deleteEdges_le {s(x, y)})⟩
  let pT : T.Path u v := ⟨p, hp⟩
  have heq : qT = pT := (hT.subsingleton_path u v).elim qT pT
  have hedgeQM : s(x, y) ∈ qT.val.edges := by
    rw [heq]
    exact he
  have hedgeQ : s(x, y) ∈ q.edges := by
    simpa [qT] using hedgeQM
  have hedgeDelete := q.edges_subset_edgeSet hedgeQ
  simp [edgeSet_deleteEdges] at hedgeDelete

private lemma exists_cut_edge_on_tree_path {T A : SimpleGraph (Fin n)} {S : Set (Fin n)}
    {u v : Fin n} (hT : T.IsTree) (hrespect : RespectsCut A S)
    (hu : u ∈ S) (hv : v ∉ S) :
    ∃ x y, T.Adj x y ∧ x ∈ S ∧ y ∉ S ∧ ¬A.Adj x y ∧
      ¬(T.deleteEdges {s(x, y)}).Reachable u v := by
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath u v
  obtain ⟨x, y, hxy, hx, hy, hnotA, he⟩ := exists_cut_edge_on_path p hrespect hu hv
  exact ⟨x, y, hxy, hx, hy, hnotA,
    not_reachable_delete_edge_of_mem_path hT.isAcyclic p hp he⟩

private lemma card_deleteEdges_sup_edge (G : SimpleGraph (Fin n)) {x y u v : Fin n}
    (hxy : G.Adj x y) (huv : u ≠ v) (hnew : ¬G.Adj u v) : by
    classical
    exact (G.deleteEdges {s(x, y)} ⊔ edge u v).edgeFinset.card = G.edgeFinset.card := by
  classical
  have hdel : (G.deleteEdges {s(x, y)}).edgeFinset = G.edgeFinset.erase s(x, y) := by
    simp only [edgeFinset, edgeSet_deleteEdges, Set.toFinset_sdiff,
      Set.toFinset_singleton, Finset.sdiff_singleton_eq_erase]
  have hedge : (edge u v).edgeFinset = {s(u, v)} := by
    simp [edgeFinset, edgeSet_edge_of_ne huv]
  have hn : s(u, v) ∉ G.edgeFinset := by simpa using hnew
  have hdis : Disjoint (G.edgeFinset.erase s(x, y)) {s(u, v)} :=
    Finset.disjoint_singleton_right.mpr (by simp [hn])
  simp only [edgeFinset_sup, hdel, hedge, Finset.card_union_of_disjoint hdis,
    Finset.card_singleton]
  exact Finset.card_erase_add_one (by simpa using hxy)

private lemma exchanged_graph_isTree {T : SimpleGraph (Fin n)} {x y u v : Fin n}
    (hT : T.IsTree) (hxy : T.Adj x y) (huv : u ≠ v) (hnew : ¬T.Adj u v)
    (hnreach : ¬(T.deleteEdges {s(x, y)}).Reachable u v) :
    (T.deleteEdges {s(x, y)} ⊔ edge u v).IsTree := by
  classical
  let : Nonempty (Fin n) := hT.connected.nonempty
  let F := T.deleteEdges {s(x, y)} ⊔ edge u v
  have hacycDelete : (T.deleteEdges {s(x, y)}).IsAcyclic :=
    IsAcyclic.anti (deleteEdges_le {s(x, y)}) hT.isAcyclic
  have hacycF : F.IsAcyclic := IsAcyclic.sup_edge_of_not_reachable hnreach hacycDelete
  obtain ⟨K, hFK, _, hKtree⟩ :=
    Connected.exists_isTree_le_of_le_of_isAcyclic (G := ⊤) (H := F)
      connected_top le_top hacycF
  have hcardT := hT.card_edgeFinset
  have hcardK := hKtree.card_edgeFinset
  have hcardF : F.edgeFinset.card = T.edgeFinset.card :=
    card_deleteEdges_sup_edge T hxy huv hnew
  have hcards : F.edgeFinset.card = K.edgeFinset.card := Nat.add_right_cancel
    (show F.edgeFinset.card + 1 = K.edgeFinset.card + 1 by rw [hcardF, hcardT, hcardK])
  have hfin := Finset.eq_of_subset_of_card_le (edgeFinset_mono hFK) hcards.ge
  have heq : F = K := edgeFinset_inj.mp hfin
  change F.IsTree
  rw [heq]
  exact hKtree

/-- A light crossing edge of the cut, with unrestricted signed real weights. -/
private def IsLightEdge (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (S : Set (Fin n)) (u v : Fin n) : Prop :=
  u ∈ S ∧ v ∉ S ∧ G.Adj u v ∧
    ∀ ⦃a b⦄, G.Adj a b → a ∈ S → b ∉ S → w s(u, v) ≤ w s(a, b)

private lemma le_deleteEdges_singleton_of_not_adj {A T : SimpleGraph (Fin n)} {x y : Fin n}
    (hAT : A ≤ T) (hnotA : ¬A.Adj x y) : A ≤ T.deleteEdges {s(x, y)} := by
  rw [← edgeSet_subset_edgeSet]
  intro e heA
  have heT := edgeSet_mono hAT heA
  have hene : e ≠ s(x, y) := by
    intro heq
    apply hnotA
    have : s(x, y) ∈ A.edgeSet := heq ▸ heA
    exact this
  simp [edgeSet_deleteEdges, heT, hene]

/-- Respected-cut exchange for unrestricted real weights on canonical simple graphs. -/
private lemma respectedCut_exchange (G T A : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (S : Set (Fin n)) (u v : Fin n) (hTG : T ≤ G) (hT : T.IsTree) (hAT : A ≤ T)
    (hrespect : RespectsCut A S) (hlight : IsLightEdge G w S u v) :
    ∃ T' : SimpleGraph (Fin n), T' ≤ G ∧ T'.IsTree ∧
      A ⊔ edge u v ≤ T' ∧ totalEdgeWeight w T' ≤ totalEdgeWeight w T := by
  classical
  rcases hlight with ⟨hu, hv, huvG, hminimum⟩
  have huv : u ≠ v := fun h ↦ hv (h ▸ hu)
  by_cases huvT : T.Adj u v
  · exact ⟨T, hTG, hT, sup_le hAT ((edge_le_iff T).mpr (Or.inr huvT)), le_rfl⟩
  obtain ⟨x, y, hxyT, hx, hy, hxyA, hnreach⟩ :=
    exists_cut_edge_on_tree_path hT hrespect hu hv
  let T' := T.deleteEdges {s(x, y)} ⊔ edge u v
  have hT'G : T' ≤ G :=
    sup_le ((deleteEdges_le {s(x, y)}).trans hTG) ((edge_le_iff G).mpr (Or.inr huvG))
  have hcontain : A ⊔ edge u v ≤ T' := sup_le
    ((le_deleteEdges_singleton_of_not_adj hAT hxyA).trans le_sup_left) le_sup_right
  refine ⟨T', hT'G, exchanged_graph_isTree hT hxyT huv huvT hnreach, hcontain, ?_⟩
  change totalEdgeWeight w (T.deleteEdges {s(x, y)} ⊔ edge u v) ≤ totalEdgeWeight w T
  rw [totalEdgeWeight_deleteEdges_sup_edge w T hxyT huv huvT]
  have hweight := hminimum (hTG hxyT) hx hy
  calc
    totalEdgeWeight w T - w s(x, y) + w s(u, v) =
        w s(u, v) + (totalEdgeWeight w T - w s(x, y)) := add_comm _ _
    _ ≤ w s(x, y) + (totalEdgeWeight w T - w s(x, y)) := add_le_add_left hweight _
    _ = totalEdgeWeight w T := by rw [add_comm, sub_add_cancel]

/-- The weight is exactly the canonical edge-finset sum. -/
private lemma totalEdgeWeight_eq_edgeFinset_sum (w : Sym2 (Fin n) → ℝ)
    (G : SimpleGraph (Fin n)) : by
    classical
    exact totalEdgeWeight w G = ∑ e ∈ G.edgeFinset, w e := by
  rfl

end SimpleGraph
