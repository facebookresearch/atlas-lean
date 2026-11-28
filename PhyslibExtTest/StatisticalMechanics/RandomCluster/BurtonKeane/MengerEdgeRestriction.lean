/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerEdgeRestriction

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerEdgeRestriction`

* `bc17_hard_bot`: in the empty graph on `Fin 3`, with both sides the whole vertex set, every
  separator has three vertices, so three disjoint (trivial) paths exist (instance).
* `bc17_minmax_one` on the path graph `pathGraph 3` with both sides the whole vertex set.
* `bc17_restr_edgeSet_ncard_lt`: restricting `pathGraph 3` to `{0, 1}` removes an edge.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MengerEdgeRestriction

open _root_.StatMech.Walls

/-- With both sides the whole vertex set, every separator is the whole vertex set: each trivial
walk must be hit. -/
theorem sep_univ {V : Type} {G : SimpleGraph V} {C : Set V}
    (hC : bc16_IsSeparator G Set.univ Set.univ C) : C = Set.univ :=
  Set.eq_univ_of_forall fun s => by
    obtain ⟨c, hc, hcs⟩ := hC (Set.mem_univ s) (Set.mem_univ s) SimpleGraph.Walk.nil
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hcs
    exact hcs ▸ hc

/-- Every separator between `univ` and `univ` in a graph on `Fin n` has `n` vertices. -/
theorem sep_card {n : ℕ} {G : SimpleGraph (Fin n)} (C : Set (Fin n))
    (hC : bc16_IsSeparator G Set.univ Set.univ C) : n ≤ C.ncard := by
  rw [sep_univ hC, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

-- Three disjoint paths in the empty graph on three vertices.
example : Nonempty (bc16_DisjointPathFamily (⊥ : SimpleGraph (Fin 3)) Set.univ Set.univ (Fin 3)) :=
  bc17_hard_bot _ _ sep_card

-- One path when every separator is nonempty.
example : ∃ _F : bc16_DisjointPathFamily (SimpleGraph.pathGraph 3) Set.univ Set.univ (Fin 1),
    ∀ C, bc16_IsSeparator (SimpleGraph.pathGraph 3) Set.univ Set.univ C →
      Fintype.card (Fin 1) ≤ C.ncard :=
  bc17_minmax_one _ _ _ fun C hC => le_trans (by norm_num) (sep_card C hC)

-- Restriction to `{0, 1}` strictly decreases the edge count of the path `0 – 1 – 2`.
example : (bc17_restr (SimpleGraph.pathGraph 3) {0, 1}).edgeSet.ncard <
    (SimpleGraph.pathGraph 3).edgeSet.ncard :=
  bc17_restr_edgeSet_ncard_lt _ _ (x := 1) (y := 2) (by simp [SimpleGraph.pathGraph_adj])
    (by decide)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MengerEdgeRestriction
