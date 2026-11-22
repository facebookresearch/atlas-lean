/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveLengthAttachment

/-!
# Complete original native word-length stage coverage

Every original full word in the next stage is either already in the
old stage or is the actual ordinal restriction of the SAME full
original path cell. Its individual endpoints, original total path and
all coefficient cuts supply the genuine indexed native range witness.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- Every full original word of the supplied length occurs in its SAME original native word-cell range. -/
lemma word_mem_stageCellMap_range (k n : ℕ) (w : (nerve (Paths V)) _⦋n⦌)
    (hw : (totalPath V n w).length = k) : w ∈ (SSet.Subcomplex.range (stageCellMap V k)).obj (op ⦋n⦌) := by
  let a : WordLabel V k := ⟨w.obj 0, w.obj (Fin.last n), totalPath V n w, hw⟩
  let c : (labelSimplex V k a) _⦋n⦌ := SSet.stdSimplex.objMk (cutOrdinal V n w)
  refine ⟨⟨a, c⟩, ?_⟩
  exact (original_word_restriction V n w).symm

/-- The SAME complete original next stage is covered by the old stage
and the full indexed native original length-cell map, with all words retained. -/
theorem lengthStage_sup_range (k : ℕ) :
    lengthStage V k ⊔ SSet.Subcomplex.range (stageCellMap V (k + 1)) = lengthStage V (k + 1) := by
  apply le_antisymm
  · exact sup_le (lengthStage_mono V (Nat.le_succ k)) (stageCellMap_range_le V (k + 1))
  · intro q w hw
    rcases q with ⟨⟨n⟩⟩
    change (totalPath V n w).length ≤ k + 1 at hw
    by_cases h : (totalPath V n w).length ≤ k
    · exact Or.inl h
    · have he : (totalPath V n w).length = k + 1 := by omega
      exact Or.inr (word_mem_stageCellMap_range V (k + 1) n w he)

end CategoryTheory.FreePathNerveCoordinates
