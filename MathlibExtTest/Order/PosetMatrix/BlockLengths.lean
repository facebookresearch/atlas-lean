/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Order.PosetMatrix.BlockLengths
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for relabeling inequivalence of block matrices
-/

namespace MetaMathlibExt.not_relabel_equiv_of_blockLengths_ne

/-- Two disjoint stars on six vertices, with the second star starting at `r`. -/
private def twoStars (r : Fin 6) : Matrix (Fin 6) (Fin 6) Bool :=
  fun i j => decide (i = j ∨ i = 0 ∧ j < r ∨ i = r ∧ r ≤ j)

-- Both matrices have four off-diagonal ones. Their block sizes are (2, 4) and (3, 3).
example : ¬ ∃ σ : Equiv.Perm (Fin 6), twoStars 3 = (twoStars 2).submatrix σ σ := by
  let l : Fin 3 → ℕ := ![0, 2, 6]
  let l' : Fin 3 → ℕ := ![0, 3, 6]
  apply not_relabel_equiv_of_blockLengths_ne 6 2 (by decide) (by decide) _ _
      (by unfold IsPosetMatrix twoStars; decide) (by unfold IsPosetMatrix twoStars; decide) l l'
  · unfold StrictMono Monotone
    decide
  · unfold StrictMono Monotone
    decide
  · unfold twoStars
    decide
  · unfold twoStars
    decide
  · intro k
    exact ⟨1, by decide, by decide +revert, by unfold twoStars; decide +revert⟩
  · intro k
    exact ⟨1, by decide, by decide +revert, by unfold twoStars; decide +revert⟩
  · exact fun h => (by decide : (2 : ℕ) ≠ 3) (congrFun h 1)

end MetaMathlibExt.not_relabel_equiv_of_blockLengths_ne
