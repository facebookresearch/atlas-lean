/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.WeightedMatroidNonnegativeLinesConnected

namespace MathlibExtTest.Combinatorics.WeightedMatroidNonnegativeLinesConnected

open MathlibExt.Combinatorics.WeightedMatroidNonnegativeLinesConnectedWanted

private abbrev M : Matroid (Fin 3) := Matroid.freeOn Set.univ

private theorem simple : IsSimpleMatroid M :=
  fun _ _ ↦ Matroid.freeOn_indep (Set.subset_univ _)

private theorem rank_three : M.eRank = 3 := by
  simp [M, Matroid.eRank_freeOn]

-- Zero-weight points are vertices and a zero-weight line gives an edge.
example : (nonnegGraph M (fun _ ↦ 0)).Adj ⟨0, le_rfl⟩ ⟨1, le_rfl⟩ := by
  apply (SimpleGraph.fromRel_adj _ _ _).2
  refine ⟨fun h ↦ by simpa using congrArg Subtype.val h, Or.inl ?_⟩
  refine ⟨{0, 1}, ⟨?_, ?_⟩, by simp [weight], by simp, by simp⟩
  · rw [Matroid.isFlat_iff_closure_eq]
    simp [M]
  · rw [Matroid.eRk_freeOn (Set.subset_univ _)]
    exact Set.encard_pair (by decide)

private def mixedWeights (i : Fin 3) : ℝ := if i = 0 then 2 else -1

-- Set weights include negative summands and exclude points outside the set.
example : weight mixedWeights ({1, 2} : Set (Fin 3)) = -2 := by
  classical
  norm_num [weight, Finset.sum_filter, Fin.sum_univ_three, mixedWeights]

-- At total weight zero, the graph may have just one vertex and is still connected.
example : (nonnegGraph M mixedWeights).Connected := by
  apply conjecture_holds 3 M mixedWeights simple rank_three rfl
  norm_num [Fin.sum_univ_three, mixedWeights]

end MathlibExtTest.Combinatorics.WeightedMatroidNonnegativeLinesConnected
