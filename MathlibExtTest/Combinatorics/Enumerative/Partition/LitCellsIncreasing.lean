/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.LitCellsIncreasing

open MetaMathlibExt PowerSeries
open scoped PowerSeries.WithPiTopology

-- Both repeated and distinct sizes occur in the partition (3, 3, 1).
example : litCellsIncreasing (Nat.Partition.ofMultiset {3, 3, 1}) = 4 := by decide

-- The empty partition contributes zero to the constant coefficient.
example :
    let P : ℤ⟦X⟧ := mk fun n => (Fintype.card (Nat.Partition n) : ℤ)
    coeff 0 (2 * P * ∑' i : ℕ, X ^ (i + 1) * invOfUnit (1 - X ^ (i + 1)) 1 -
      P * X * invOfUnit (1 - X) 1) = 0 := by
  dsimp only
  rw [← litCellsIncreasing_generatingFunction.1]
  simp [litCellsIncreasing]

-- The first positive coefficient counts the single lit cell of the partition (1).
example :
    let P : ℤ⟦X⟧ := mk fun n => (Fintype.card (Nat.Partition n) : ℤ)
    coeff 1 (P * ∑' i : ℕ, X ^ (i + 1) * (1 + X ^ (i + 1)) *
      invOfUnit (1 - X ^ (i + 1)) 1) = 1 := by
  dsimp only
  rw [← litCellsIncreasing_generatingFunction.2, coeff_mk]
  simp [litCellsIncreasing]
