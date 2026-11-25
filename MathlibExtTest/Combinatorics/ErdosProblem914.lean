/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ErdosProblem914
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! # Degree thresholds for clique factors and equitable colourings -/

open MathlibExt.Combinatorics.ErdosProblem914Wanted
open SimpleGraph

-- At the minimum-degree threshold, two disjoint edges cover the four-cycle.
example : ∃ A B : Finset (Fin 4), (cycleGraph 4).IsNClique 2 A ∧
    (cycleGraph 4).IsNClique 2 B ∧ Disjoint A B ∧ A ∪ B = Finset.univ := by
  have hdeg : 2 ≤ (cycleGraph 4).minDegree :=
    (cycleGraph 4).le_minDegree_of_forall_le_degree _ fun _ =>
      (cycleGraph_degree_three_le (n := 1)).ge
  obtain ⟨K, hK, hd⟩ := conjecture_holds.{0, 0}.1 (r := 2) (m := 2) (by decide) (by decide)
    (cycleGraph 4) (by decide) hdeg
  have hd01 := hd (show (0 : Fin 2) ≠ 1 by decide)
  refine ⟨K 0, K 1, hK 0, hK 1, hd01, Finset.eq_univ_of_card _ ?_⟩
  rw [Finset.card_union_of_disjoint hd01, (hK 0).card_eq, (hK 1).card_eq]
  decide

-- At the one-colour boundary, the sole class contains all vertices of an edgeless graph.
example {r : ℕ} (hr : 2 ≤ r) : ∃ C : (⊥ : SimpleGraph (Fin r)).Coloring (Fin 1),
    (C.colorClass 0).ncard = r ∧ C.colorClass 0 = Set.univ := by
  obtain ⟨C, hC⟩ := conjecture_holds.{0, 0}.2 (m := 1) hr (by decide)
    (⊥ : SimpleGraph (Fin r)) (by simp) (by simp)
  exact ⟨C, hC 0, Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _⟩
