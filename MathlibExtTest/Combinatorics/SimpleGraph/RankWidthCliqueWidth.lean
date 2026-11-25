/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.RankWidthCliqueWidth
import Mathlib.Combinatorics.SimpleGraph.Star

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.RankWidthCliqueWidth

open _root_.SimpleGraph

-- The three leaves of a star give a decomposition with an internal branching node.
private def threeLeaves : RankDecomposition (Fin 3) := by
  let T := starGraph (none : Option (Fin 3))
  have hc : (T.neighborSet none).ncard = 3 := by
    have he : T.neighborSet none = Set.range some := by
      ext i
      cases i <;> simp [T, starGraph_adj]
    rw [he, Set.ncard_range_of_injective (Option.some_injective _)]
    simp
  have hl (i : Fin 3) : (T.neighborSet (some i)).ncard = 1 := by
    have he : T.neighborSet (some i) = {none} := by
      ext j
      cases j <;> simp [T, starGraph_adj]
    simp [he]
  exact {
    ι := Option (Fin 3)
    T := T
    isTree := isTree_starGraph _
    degree_one_or_three := fun
      | none => Or.inr hc
      | some j => Or.inl (hl j)
    leaf := Function.Embedding.some
    range_leaf := by
      ext i
      change (∃ j : Fin 3, some j = i) ↔ (T.neighborSet i).ncard = 1
      cases i with
      | none => rw [hc]; simp
      | some j => rw [hl]; simp }

-- The shared zero label suffices even for a nonempty decomposition with several leaves.
example : (⊥ : SimpleGraph (Fin 3)).HasCliqueWidthAtMost 1 := by
  have hw : (⊥ : SimpleGraph (Fin 3)).HasRankWidthAtMost 0 := by
    refine Or.inr ⟨threeLeaves, fun i j _ => ?_⟩
    classical
    unfold cutRank
    let S := threeLeaves.side i j
    apply le_of_eq
    trans (0 : Matrix S ↥Sᶜ (ZMod 2)).rank
    · apply congrArg Matrix.rank
      ext
      simp
    · exact Matrix.rank_zero
  exact hw.hasCliqueWidthAtMost

-- Nonzero cut rows occur on every leaf cut of the triangle.
example : (⊤ : SimpleGraph (Fin 3)).HasCliqueWidthAtMost 3 := by
  have hw : (⊤ : SimpleGraph (Fin 3)).HasRankWidthAtMost 1 :=
    Or.inr ⟨threeLeaves, fun _ _ _ => cutRank_top_le_one _⟩
  exact hw.hasCliqueWidthAtMost

-- The empty graph and the one-vertex graph use the small-cardinality convention.
example (G : SimpleGraph (Fin 0)) : G.HasCliqueWidthAtMost 1 :=
  (hasRankWidthAtMost_of_card_le_one G (by simp) 0).hasCliqueWidthAtMost

example (G : SimpleGraph (Fin 1)) : G.HasCliqueWidthAtMost 1 :=
  (hasRankWidthAtMost_of_card_le_one G (by simp) 0).hasCliqueWidthAtMost

end MathlibExtTest.Combinatorics.SimpleGraph.RankWidthCliqueWidth
