/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Order.PosetMatrix.BlockDecomposition

/-!
# Tests for block decomposition of a poset matrix
-/

namespace MetaMathlibExt.isPosetMatrix_block_iff_directSum_ordinalSum

open Matrix

-- Two incomparable elements lie below a common top.
private def fork : Matrix (Fin 3) (Fin 3) Bool := fun i j => decide (i = j ∨ j = 2)

private theorem fork_poset : IsPosetMatrix 3 fork := by
  unfold IsPosetMatrix fork
  decide

-- The cut just before the top yields an ordinal sum.
example : ∃ A : Matrix (Fin 2) (Fin 2) Bool, ∃ B : Matrix (Fin 1) (Fin 1) Bool,
    IsPosetMatrix 2 A ∧ IsPosetMatrix 1 B ∧ fork = reindex finSumFinEquiv finSumFinEquiv
      (fromBlocks A (Matrix.of fun _ _ => true) (Matrix.of fun _ _ => false) B) := by
  apply (isPosetMatrix_block_iff_directSum_ordinalSum 2 1 (by decide) (by decide) fork
    fork_poset).2.mp
  intro i j _ hj
  have hj' : j = 2 := Fin.ext (by change j.val = 2; omega)
  simp [fork, hj']

-- The earlier cut has both a false and a true entry in its upper-right block.
example (b : Bool) : ¬ ∃ A : Matrix (Fin 1) (Fin 1) Bool, ∃ B : Matrix (Fin 2) (Fin 2) Bool,
    IsPosetMatrix 1 A ∧ IsPosetMatrix 2 B ∧ fork = reindex finSumFinEquiv finSumFinEquiv
      (fromBlocks A (Matrix.of fun _ _ => b) (Matrix.of fun _ _ => false) B) := by
  have h := isPosetMatrix_block_iff_directSum_ordinalSum 1 2 (by decide) (by decide) fork fork_poset
  cases b
  · intro hd
    exact Bool.noConfusion (h.1.mpr hd 0 2 (by decide) (by decide))
  · intro ho
    exact Bool.noConfusion (h.2.mpr ho 0 1 (by decide) (by decide))

end MetaMathlibExt.isPosetMatrix_block_iff_directSum_ordinalSum
