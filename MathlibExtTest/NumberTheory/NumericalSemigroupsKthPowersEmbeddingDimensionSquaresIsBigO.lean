/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NumericalSemigroupsKthPowersEmbeddingDimensionSquaresIsBigO

/-!
# Tests for the linear embedding dimension of square semigroups

Apply the uniform bound to starting indices `2` and `3`, and derive a bound for shifted tails.
-/

namespace MathlibExtTest.NumberTheory.NumericalSemigroupsKthPowersEmbeddingDimensionSquaresIsBigO

private abbrev minimalSquares (n : ℕ) : Set ℕ :=
  {s | s ∈ AddSubmonoid.closure ((fun i => i ^ 2) '' Set.Ici n) ∧ s ≠ 0 ∧
    ∀ a ∈ AddSubmonoid.closure ((fun i => i ^ 2) '' Set.Ici n),
      ∀ b ∈ AddSubmonoid.closure ((fun i => i ^ 2) '' Set.Ici n),
        a + b = s → a = 0 ∨ b = 0}

example : ∃ C : ℕ, (minimalSquares 2).ncard ≤ 2 * C ∧
    (minimalSquares 3).ncard ≤ 3 * C := by
  obtain ⟨C, hC⟩ := MetaMathlibExt.embeddingDimension_squares_isBigO
  exact ⟨C, by simpa [Nat.mul_comm] using hC 2 (by decide),
    by simpa [Nat.mul_comm] using hC 3 (by decide)⟩

example : ∃ C : ℕ, ∀ m : ℕ, (minimalSquares (m + 2)).ncard ≤ C * (m + 1) := by
  obtain ⟨C, hC⟩ := MetaMathlibExt.embeddingDimension_squares_isBigO
  refine ⟨2 * C, fun m => ?_⟩
  calc
    _ ≤ C * (m + 2) := hC (m + 2) (by omega)
    _ ≤ C * (2 * (m + 1)) := Nat.mul_le_mul_left C (by omega)
    _ = (2 * C) * (m + 1) := by ac_rfl

end MathlibExtTest.NumberTheory.NumericalSemigroupsKthPowersEmbeddingDimensionSquaresIsBigO
