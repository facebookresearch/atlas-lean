/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Sum
import MathlibExt.Combinatorics.ArithmeticalStructureCoconutTreeCoconutSmoothLeaf
import all MathlibExt.Combinatorics.ArithmeticalStructureCoconutTreeCoconutSmoothPath

open MetaMathlibExt
open MetaMathlibExt.IsArithmeticalStructure.coconutSmoothPath

private def starLabels : (Fin 1 ⊕ Fin 4 → ℕ) × (Fin 1 ⊕ Fin 4 → ℕ) :=
  (Sum.elim ![2] ![2, 1, 3, 6], Sum.elim ![6] ![3, 6, 2, 1])

private theorem starStructure :
    IsArithmeticalStructure (coconutTree 1 4) starLabels.1 starLabels.2 := by
  refine ⟨by decide, by decide, ?_, fun _ hg => Nat.dvd_one.mp (hg (.inr 3))⟩
  rintro (j | j)
  · rw [Subsingleton.elim j 0, path_neighborSum]
    change starLabels.1 (.inl 0) * starLabels.2 (.inl 0) =
      levelSum starLabels.2 0 + levelSum starLabels.2 2
    rw [levelSum_zero, levelSum_leaves]
    decide
  · rw [leaf_neighborSum (by decide)]
    decide +revert

-- Delete the second leaf: the leaves after it shift down, while the centre's d-label drops to 1.
example : IsArithmeticalStructure (coconutTree 1 3)
    (Sum.elim ![1] ![2, 3, 6]) (Sum.elim ![6] ![3, 2, 1]) := by
  let l : Fin 4 := 1
  have h := starStructure.coconutSmoothLeaf (s := 3) (by decide) l (by decide)
  have hlabels : coconutSmoothLeaf l starLabels =
      (Sum.elim ![1] ![2, 3, 6], Sum.elim ![6] ![3, 2, 1]) := by decide
  rwa [hlabels] at h

-- The operation also supports deleting the last remaining leaf, leaving only path vertices.
example : coconutSmoothLeaf (s := 0) 0
    (Sum.elim ![1, 2] ![1], Sum.elim ![1, 1] ![1]) =
    (Sum.elim ![1, 1] Fin.elim0, Sum.elim ![1, 1] Fin.elim0) := by
  decide
