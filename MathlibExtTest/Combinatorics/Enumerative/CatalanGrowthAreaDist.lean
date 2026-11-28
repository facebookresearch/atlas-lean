/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.Combinatorics.Enumerative.CatalanGrowthAreaDist

open MetaMathlibExt Polynomial

-- The empty word has no final letter.
example : catalanGrowthWords 0 3 = ∅ := by decide

-- At length one, the first and last letters must coincide.
example : catalanGrowthAreaDist 1 3 3 = X ^ 3 ∧ catalanGrowthAreaDist 1 3 2 = 0 := by
  constructor
  · simpa using (catalanGrowthAreaDist_succ 2 3 3 (by decide) (by decide) (by decide)).2
  · simpa using (catalanGrowthAreaDist_succ 2 3 2 (by decide) (by decide) (by decide)).2

-- From 2 to 3 in three letters, the middle letter can be 2 or 3. The jump 1 to 3 is too large.
example : catalanGrowthAreaDist 3 3 2 = X ^ 7 + X ^ 8 := by
  have hwords : ((catalanGrowthWords 3 3).filter fun w => ∀ i : Fin 3, i.val = 0 → w i = 2) =
      {![2, 2, 3], ![2, 3, 3]} := by decide
  have hne : (![2, 2, 3] : Fin 3 → ℕ) ≠ ![2, 3, 3] := by decide
  rw [catalanGrowthAreaDist, hwords]
  simp [areaDist, hne, wordArea, Fin.sum_univ_succ]
