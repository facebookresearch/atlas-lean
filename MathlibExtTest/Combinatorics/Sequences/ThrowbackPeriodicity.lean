/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Sequences.ThrowbackPeriodicity

/-!
# Partial placement periods for the positive integers

At stage one, shifting by four across the anchor preserves both a newly filled position
and a position that stays vacant.
-/

namespace MetaMathlibExt

private def positiveIntegers (i : ℕ) : ℕ := i + 1

private theorem stageZeroAnchor : sInf {i : ℕ | partialPlacement positiveIntegers 0 i = none} = 1 := by
  apply IsLeast.csInf_eq
  constructor
  · change partialPlacement positiveIntegers 0 1 = none
    simp only [partialPlacement, positiveIntegers]
    decide
  · intro i hi
    by_contra! h
    obtain rfl : i = 0 := by omega
    change partialPlacement positiveIntegers 0 0 = none at hi
    simp [partialPlacement] at hi

example : partialPlacement positiveIntegers 1 (-3) = some 2 ∧
    partialPlacement positiveIntegers 1 1 = some 2 := by
  constructor <;> rw [partialPlacement] <;> dsimp only <;> rw [stageZeroAnchor] <;>
    simp only [partialPlacement, positiveIntegers] <;> decide

example : partialPlacement positiveIntegers 1 (-1) = none ∧
    partialPlacement positiveIntegers 1 3 = none := by
  constructor <;> rw [partialPlacement] <;> dsimp only <;> rw [stageZeroAnchor] <;>
    simp only [partialPlacement, positiveIntegers] <;> decide

example (n : ℕ) : ∃ p : ℤ, 0 < p ∧
    ∀ z, partialPlacement positiveIntegers n (z + p) = partialPlacement positiveIntegers n z :=
  partialPlacement_periodic positiveIntegers (fun _ _ h => Nat.succ_lt_succ h) (by decide) n

end MetaMathlibExt
