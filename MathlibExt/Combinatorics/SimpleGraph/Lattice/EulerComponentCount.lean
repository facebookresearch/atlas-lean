/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanCycleSpace

/-!
# Component counts after deleting edges

Deleting one edge from a graph keeps the number of components if the edge is not a bridge and adds
one component if it is. Hence deleting a finite set `B` of edges adds at most `|B|` components, and
`c + |E| = |V| + nullity`. A connected graph from which a bridge is deleted has exactly two
components, which is the component count of the dual of a cycle.

## Main definitions

* `StatMech.Lattice.ecc_DualCutModel A B' a b`: `A` minus `B'` is connected and `{a, b}` is a bridge
  of it.

## Main results

* `StatMech.Lattice.ecc_deleteEdge_card_nonbridge`, `StatMech.Lattice.ecc_deleteEdge_card_bridge`:
  deleting a non-bridge or a bridge.
* `StatMech.Lattice.ecc_deleteEdges_finset_card_le`: deleting `|B|` edges adds at most `|B|`
  components.
* `StatMech.Lattice.ecc_comp_add_edges_eq_card_add_nullity`: `c + |E| = |V| + nullity`.
* `StatMech.Lattice.ecc_two_components_of_dualModel`: in a dual cut model the deletion has two
  components.
-/

@[expose] public section

open SimpleGraph Set

set_option linter.unusedSectionVars false

namespace StatMech

namespace Lattice

variable {V : Type*} [Finite V] [DecidableEq V]

omit [DecidableEq V] in
theorem ecc_deleteEdge_card_nonbridge (A : SimpleGraph V) {a b : V}
    (he : s(a, b) ∈ A.edgeSet) (hr : (A.deleteEdges {s(a, b)}).Reachable a b) :
    Nat.card (A.deleteEdges {s(a, b)}).ConnectedComponent = Nat.card A.ConnectedComponent := by
  classical
  have hAeq : A = A.deleteEdges {s(a, b)} ⊔ edge a b := deleteEdges_sup_edge_eq A a b he
  have hh := card_components_sup_edge_of_reachable (A.deleteEdges {s(a, b)}) a b hr
  rw [← hAeq] at hh; omega

omit [DecidableEq V] in
theorem ecc_deleteEdge_card_bridge (A : SimpleGraph V) {a b : V}
    (he : s(a, b) ∈ A.edgeSet) (hr : ¬ (A.deleteEdges {s(a, b)}).Reachable a b) :
    Nat.card (A.deleteEdges {s(a, b)}).ConnectedComponent
      = Nat.card A.ConnectedComponent + 1 := by
  classical
  have hAeq : A = A.deleteEdges {s(a, b)} ⊔ edge a b := deleteEdges_sup_edge_eq A a b he
  have hh := card_components_sup_edge_of_not_reachable (A.deleteEdges {s(a, b)}) a b hr
  rw [← hAeq] at hh; omega

omit [DecidableEq V] in
theorem ecc_deleteEdge_card_le (A : SimpleGraph V) (e : Sym2 V) :
    Nat.card (A.deleteEdges {e}).ConnectedComponent ≤ Nat.card A.ConnectedComponent + 1 := by
  classical
  by_cases he : e ∈ A.edgeSet
  · induction e with
    | _ a b =>
      by_cases hr : (A.deleteEdges {s(a, b)}).Reachable a b
      · rw [ecc_deleteEdge_card_nonbridge A he hr]; omega
      · rw [ecc_deleteEdge_card_bridge A he hr]
  · rw [SimpleGraph.deleteEdges_eq_self.mpr
      (by rw [Set.disjoint_singleton_right]; exact he)]
    omega

omit [DecidableEq V] in
theorem ecc_deleteEdge_card_ge (A : SimpleGraph V) (e : Sym2 V) :
    Nat.card A.ConnectedComponent ≤ Nat.card (A.deleteEdges {e}).ConnectedComponent :=
  ConnectedComponent.card_le_card_of_le (deleteEdges_le _)

omit [DecidableEq V] in
theorem ecc_deleteEdges_finset_card_le (A : SimpleGraph V) (B : Finset (Sym2 V)) :
    Nat.card (A.deleteEdges ↑B).ConnectedComponent ≤ Nat.card A.ConnectedComponent + B.card := by
  classical
  induction B using Finset.induction with
  | empty => simp
  | @insert e s hes ih =>
    have hdec : A.deleteEdges ↑(insert e s) = (A.deleteEdges ↑s).deleteEdges {e} := by
      rw [Finset.coe_insert, SimpleGraph.deleteEdges_deleteEdges]
      congr 1; rw [Set.union_singleton]
    rw [hdec]
    have h1 := ecc_deleteEdge_card_le (A.deleteEdges ↑s) e
    rw [Finset.card_insert_of_notMem hes]
    omega

omit [DecidableEq V] in
theorem ecc_comp_add_edges_eq_card_add_nullity (A : SimpleGraph V) :
    Nat.card A.ConnectedComponent + A.edgeSet.ncard = Nat.card V + nullity A := by
  classical
  have hbound := card_le_edgeSet_add_components A
  unfold nullity
  omega

omit [DecidableEq V] in
theorem ecc_two_components_tree_plus_bridge (A : SimpleGraph V) (B' : Set (Sym2 V)) {a b : V}
    (hconn : (A.deleteEdges B').Connected)
    (he : s(a, b) ∈ (A.deleteEdges B').edgeSet)
    (hbridge : ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b) :
    Nat.card ((A.deleteEdges B').deleteEdges {s(a, b)}).ConnectedComponent = 2 := by
  classical
  rw [ecc_deleteEdge_card_bridge (A.deleteEdges B') he hbridge,
    card_components_eq_one_of_connected hconn]

omit [DecidableEq V] in
theorem ecc_bridge_adds_one_component (A : SimpleGraph V) (B' : Set (Sym2 V)) {a b : V}
    (he : s(a, b) ∈ (A.deleteEdges B').edgeSet)
    (hbridge : ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b) :
    Nat.card ((A.deleteEdges B').deleteEdges {s(a, b)}).ConnectedComponent
      = Nat.card (A.deleteEdges B').ConnectedComponent + 1 :=
  ecc_deleteEdge_card_bridge (A.deleteEdges B') he hbridge

/-- After deleting the edges `B'`, the graph `A` is connected and `{a, b}` is one of its bridges. -/
def ecc_DualCutModel (A : SimpleGraph V) (B' : Set (Sym2 V)) (a b : V) : Prop :=
  (A.deleteEdges B').Connected ∧
    s(a, b) ∈ (A.deleteEdges B').edgeSet ∧
    ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b

omit [DecidableEq V] in
theorem ecc_two_components_of_dualModel (A : SimpleGraph V) (B' : Set (Sym2 V)) {a b : V}
    (h : ecc_DualCutModel A B' a b) :
    Nat.card ((A.deleteEdges B').deleteEdges {s(a, b)}).ConnectedComponent = 2 := by
  obtain ⟨hconn, he, hbridge⟩ := h
  exact ecc_two_components_tree_plus_bridge A B' hconn he hbridge

omit [DecidableEq V] in
theorem ecc_cycle_dual_two_components {W : Type*} [Finite W]
    {G : SimpleGraph W} {w : W}
    (c : G.Walk w w) (hc : c.IsCycle)
    (A : SimpleGraph V) (B' : Set (Sym2 V)) {a b : V} (h : ecc_DualCutModel A B' a b) :
    faceCount c.toSubgraph.coe = 2 ∧
      Nat.card ((A.deleteEdges B').deleteEdges {s(a, b)}).ConnectedComponent = 2 := by
  classical
  exact ⟨jcs_cycle_faceCount_eq_two c hc, ecc_two_components_of_dualModel A B' h⟩

theorem ecc_dualModel_triangle :
    ecc_DualCutModel (⊤ : SimpleGraph (Fin 3)) {s(0, 1)} 1 2 :=
  ⟨by decide, by decide, by decide⟩

theorem ecc_two_components_triangle :
    Nat.card (((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(0, 1)}).deleteEdges
      {s(1, 2)}).ConnectedComponent = 2 :=
  ecc_two_components_of_dualModel (⊤ : SimpleGraph (Fin 3)) {s(0, 1)} ecc_dualModel_triangle

end Lattice

end StatMech
