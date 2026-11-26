/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FiniteCutHubCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FiniteCutHubCount`

On the star with centre `0` and leaves `1, 2, 3` (on `Fin 4`):
* `finite_cutHub_count` with hub set `{0}` and boundary `{1, 2, 3}` (deleting the centre separates
  the leaves);
* `finite_cutHub_count_of_ambient` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FiniteCutHubCount

open _root_.StatMech.FK.TriHex

/-- The star with centre `0` and leaves `1, 2, 3`. -/
def star : SimpleGraph (Fin 4) := SimpleGraph.fromEdgeSet {s(0, 1), s(0, 2), s(0, 3)}

instance : DecidableRel star.Adj := fun a b => by
  unfold star; simp only [SimpleGraph.fromEdgeSet_adj]; infer_instance

/-- Deleting the edges at the centre leaves no edge. -/
theorem star_del_no_adj (a b : Fin 4) : ¬ (star.deleteIncidenceSet 0).Adj a b := by
  rw [SimpleGraph.deleteIncidenceSet_adj]
  revert a b; decide

/-- Distinct leaves are not reachable once the centre's edges are deleted. -/
theorem star_cut {a b : Fin 4} (hab : a ≠ b) : ¬ (star.deleteIncidenceSet 0).Reachable a b := by
  rintro ⟨p⟩
  cases p with
  | nil => exact hab rfl
  | cons h _ => exact star_del_no_adj _ _ h

/-- Removing an edge at a leaf leaves the leaf without neighbours. -/
theorem star_leaf_isolated : ∀ a b x : Fin 4, a ≠ 0 → star.Adj a b →
    ¬ (star.deleteEdges {s(a, b)}).Adj a x := by
  simp only [star, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_insert_iff,
    Set.mem_singleton_iff, Sym2.eq_iff]
  decide

/-- An edge at a leaf is a bridge. -/
theorem star_leaf_bridge {a b : Fin 4} (ha : a ≠ 0) (hab : star.Adj a b) :
    ¬ (star.deleteEdges {s(a, b)}).Reachable a b := by
  rintro ⟨p⟩
  cases p with
  | nil => exact hab.ne rfl
  | cons h _ => exact star_leaf_isolated _ _ _ ha hab h

/-- The star is acyclic. -/
theorem star_acyclic : star.IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_isBridge]
  intro e he
  induction e using Sym2.ind with
  | _ v w =>
  have hvw : star.Adj v w := he
  rw [SimpleGraph.isBridge_iff]
  by_cases hv : v = 0
  · subst hv
    have hw : w ≠ 0 := hvw.ne.symm
    rw [Sym2.eq_swap]
    exact fun h => star_leaf_bridge hw hvw.symm h.symm
  · exact star_leaf_bridge hv hvw

-- The centre is a cut hub with three boundary arms.
example : ({0} : Finset (Fin 4)).card ≤ ({1, 2, 3} : Finset (Fin 4)).card :=
  finite_cutHub_count star star_acyclic {0} {1, 2, 3} fun u hu => by
    rw [Finset.mem_singleton] at hu
    subst hu
    refine ⟨1, 2, 3, by decide, by decide, by decide, by decide, by decide, by decide,
      (show star.Adj 0 1 by decide).reachable, (show star.Adj 0 2 by decide).reachable,
      (show star.Adj 0 3 by decide).reachable, star_cut (by decide), star_cut (by decide),
      star_cut (by decide)⟩

-- The ambient version.
example {V : Type} [DecidableEq V] (A : SimpleGraph V) [DecidableRel A.Adj]
    (hubs boundary : Finset V)
    (harms : ∀ u ∈ hubs, ∃ t1 t2 t3 : V, t1 ∈ boundary ∧ t2 ∈ boundary ∧ t3 ∈ boundary ∧
      u ≠ t1 ∧ u ≠ t2 ∧ u ≠ t3 ∧ A.Reachable u t1 ∧ A.Reachable u t2 ∧ A.Reachable u t3 ∧
      ¬ (A.deleteIncidenceSet u).Reachable t1 t2 ∧ ¬ (A.deleteIncidenceSet u).Reachable t1 t3 ∧
      ¬ (A.deleteIncidenceSet u).Reachable t2 t3) :
    hubs.card ≤ boundary.card :=
  finite_cutHub_count_of_ambient A hubs boundary harms

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FiniteCutHubCount
