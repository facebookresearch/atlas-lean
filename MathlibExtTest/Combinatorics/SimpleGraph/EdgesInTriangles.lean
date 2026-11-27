/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.EdgesInTriangles
import Mathlib.Tactic.NormNum

namespace MathlibExt.Combinatorics.ErdosProblem905Wanted

/-- The three edges of the complete graph on three vertices meet the strict density hypothesis. -/
example : ∃ e : (⊤ : SimpleGraph (Fin 3)).edgeSet,
    0 < ((⊤ : SimpleGraph (Fin 3)).trianglesContaining e).card := by
  obtain ⟨e, he⟩ := conjecture_holds 3 ⊤ (by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
    norm_num [Nat.choose])
  refine ⟨e, ?_⟩
  exact_mod_cast (show (0 : ℝ) < ((⊤ : SimpleGraph (Fin 3)).trianglesContaining e).card from
    lt_of_lt_of_le (by norm_num) he)

/-- At the threshold, the two-vertex complete graph has one edge and no triangle through it. -/
example : ((⊤ : SimpleGraph (Fin 2)).edgeFinset.card : ℝ) = 2 ^ 2 / 4 ∧
    ∀ e : (⊤ : SimpleGraph (Fin 2)).edgeSet,
      (⊤ : SimpleGraph (Fin 2)).trianglesContaining e = ∅ := by
  constructor
  · rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
    norm_num [Nat.choose]
  · intro e
    have hf : (⊤ : SimpleGraph (Fin 2)).CliqueFree 3 :=
      SimpleGraph.cliqueFree_of_card_lt (by decide)
    simp only [SimpleGraph.trianglesContaining, Finset.filter_eq_empty_iff,
      SimpleGraph.mem_cliqueFinset_iff]
    exact fun t ht => (hf t ht).elim

end MathlibExt.Combinatorics.ErdosProblem905Wanted
