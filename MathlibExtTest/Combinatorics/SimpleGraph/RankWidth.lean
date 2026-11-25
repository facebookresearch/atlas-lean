/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.RankWidth
public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.RankWidth

open _root_.SimpleGraph

private theorem neighborSet_pathGraph_two (i : Fin 2) :
    ((pathGraph 2).neighborSet i).ncard = 1 := by
  rw [Set.ncard_eq_one]
  refine ⟨1 - i, ?_⟩
  ext j
  fin_cases i <;> fin_cases j <;> simp [pathGraph_adj]

-- Non-vacuity: the two-leaf tree is a rank-decomposition of a two-element vertex type.
private def twoLeaves : RankDecomposition (Fin 2) where
  ι := Fin 2
  T := pathGraph 2
  isTree := isTree_pathGraph.mpr (by decide)
  degree_one_or_three i := Or.inl (neighborSet_pathGraph_two i)
  leaf := Function.Embedding.refl _
  range_leaf := by
    ext i
    exact ⟨fun _ => neighborSet_pathGraph_two i, fun _ => ⟨i, rfl⟩⟩

-- The complete graph on two vertices has rank-width at most one, witnessed by this decomposition.
example : (⊤ : SimpleGraph (Fin 2)).HasRankWidthAtMost 1 :=
  Or.inr ⟨twoLeaves, fun _ _ _ => cutRank_top_le_one _⟩

-- Graphs with at most one vertex have rank-width zero.
example (G : SimpleGraph (Fin 1)) : G.HasRankWidthAtMost 0 :=
  hasRankWidthAtMost_of_card_le_one G (by simp) 0

-- Local complementation preserves rank-width bounds.
example (G : SimpleGraph (Fin 5)) (k : ℕ) (h : G.HasRankWidthAtMost k) :
    (G.localComplement 2).HasRankWidthAtMost k :=
  (hasRankWidthAtMost_localComplement_iff G 2 k).mpr h

-- Monotonicity.
example (G : SimpleGraph (Fin 5)) (h : G.HasRankWidthAtMost 1) : G.HasRankWidthAtMost 3 :=
  h.mono (by decide)

end MathlibExtTest.Combinatorics.SimpleGraph.RankWidth
