/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.ErdosStoneEdges

@[expose] public section

open Filter Finset SimpleGraph MathlibExt.Combinatorics.SimpleGraph.ErdosStoneEdges

namespace MathlibExtTest.Combinatorics.SimpleGraph.ErdosStoneEdges

/-- In `K_4` every vertex has three neighbours inside the whole vertex set. -/
example (v : Fin 4) : degIn (⊤ : SimpleGraph (Fin 4)) univ v = 3 := by
  revert v; decide

/-- `K_4` has `12 = 2 · 6` ordered adjacent pairs. -/
example : adjPairsIn (⊤ : SimpleGraph (Fin 4)) univ = 12 := by decide

/-- The deletion lemma applied to `K_4` with `β = 1/2` and `Φ₀ = 0`: the whole vertex set already
qualifies (`12 - (1/2) · 4 · 5 = 2 ≥ 0`). -/
example : ∃ T ⊆ (univ : Finset (Fin 4)),
    (0 : ℝ) ≤ adjPairsIn (⊤ : SimpleGraph (Fin 4)) T - 1 / 2 * #T * (#T + 1) ∧
      ∀ v ∈ T, 1 / 2 * (#T : ℝ) ≤ degIn (⊤ : SimpleGraph (Fin 4)) T v := by
  refine exists_subset_forall_le_degIn _ _ _ _ ?_
  have h : adjPairsIn (⊤ : SimpleGraph (Fin 4)) univ = 12 := by decide
  rw [h]
  simp
  norm_num

/-- Erdős–Stone for triangles with parts of size two: dense enough graphs contain the octahedron
`K_3(2)`. -/
example : ∀ᶠ n in atTop, ∀ {G : SimpleGraph (Fin n)} [DecidableRel G.Adj],
    (#G.edgeFinset : ℝ) ≥ (1 - 1 / (2 : ℕ) + 1 / 10) * n ^ 2 / 2 →
      completeEquipartiteGraph (2 + 1) 2 ⊑ G :=
  eventually_completeEquipartiteGraph_isContained_of_card_edgeFinset (by norm_num) 2
    (by norm_num)

end MathlibExtTest.Combinatorics.SimpleGraph.ErdosStoneEdges
