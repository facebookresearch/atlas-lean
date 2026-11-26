/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.TreeTripod
public import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.TreeTripod`

* The hypotheses of the tripod lemmas are satisfiable: the star graph on `Fin 4` centred at `0`
  is a tree (`SimpleGraph.isTree_starGraph`) whose centre has degree `3`, so
  `ftt_finite_tree_tripod` and `ftt_finite_tree_tripod_with_stems` apply.
* `ftt_tree_two_leaves` applies to the path graph on `Fin 3`.
* `ftt_neighbors_separated` on the star graph: two leaves are disconnected after deleting the
  edges at the centre.
-/

@[expose] public section

open SimpleGraph StatMech.Percolation

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.TreeTripod

/-- The centre of the star graph on `Fin 4` has degree `3`. -/
theorem star_degree_center : (starGraph (0 : Fin 4)).degree 0 = 3 := by decide

/-- The tripod at the centre of the star graph on `Fin 4`. -/
example : ∃ l : Fin 3 → Fin 4, Function.Injective l ∧
    (∀ i, (starGraph (0 : Fin 4)).degree (l i) = 1) ∧
    (∀ i j, i ≠ j → ¬ ((starGraph (0 : Fin 4)).deleteIncidenceSet 0).Reachable (l i) (l j)) :=
  ftt_finite_tree_tripod _ (isTree_starGraph 0) (by rw [star_degree_center])

/-- The tripod with stems at the centre of the star graph on `Fin 4`. -/
example : ∃ stem leaf : Fin 3 → Fin 4, Function.Injective stem ∧
    (∀ i, (starGraph (0 : Fin 4)).Adj 0 (stem i)) ∧ Function.Injective leaf ∧
    (∀ i, (starGraph (0 : Fin 4)).degree (leaf i) = 1) ∧
    (∀ i, ((starGraph (0 : Fin 4)).deleteIncidenceSet 0).Reachable (stem i) (leaf i)) ∧
    (∀ i j, i ≠ j →
      ¬ ((starGraph (0 : Fin 4)).deleteIncidenceSet 0).Reachable (leaf i) (leaf j)) :=
  ftt_finite_tree_tripod_with_stems _ (isTree_starGraph 0) (by rw [star_degree_center])

/-- The path graph on three vertices has two distinct leaves. -/
example : ∃ a b : Fin 3, a ≠ b ∧ (pathGraph 3).degree a = 1 ∧ (pathGraph 3).degree b = 1 :=
  ftt_tree_two_leaves _ (isTree_pathGraph_add_one 2) (by simp)

/-- Leaves `1` and `2` of the star graph are separated by deleting the edges at the centre. -/
example : ¬ ((starGraph (0 : Fin 4)).deleteIncidenceSet 0).Reachable 1 2 :=
  ftt_neighbors_separated _ (isAcyclic_starGraph 0) (by simp) (by simp) (by decide)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.TreeTripod
