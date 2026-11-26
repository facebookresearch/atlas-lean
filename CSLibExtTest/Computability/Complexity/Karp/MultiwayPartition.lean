/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.Karp.MultiwayPartition
import Mathlib.Tactic.IntervalCases

/-! # Boundary tests for encoded MULTIWAY NUMBER PARTITION -/

namespace MetaMathlibExt.Complexity.NPComplete.MultiwayPartition.Tests

open BitstringEncoding

-- Equal values at distinct positions can go in distinct parts.
example : multiwayPartitionDec (bitEncode (([3, 3, 3], 3) : MultiwayPartitionInstance)) =
    true := by
  simp only [multiwayPartitionDec, bitDecode_bitEncode, decide_eq_true_eq]
  refine ⟨[0, 1, 2], rfl, by decide, ?_, ?_, 3, ?_⟩
  · intro j hj
    change j < 3 at hj
    interval_cases j <;> decide
  · intro p hp
    change p < 3 at hp
    interval_cases p
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩
  · intro p hp
    change p < 3 at hp
    interval_cases p <;> decide

-- A zero still occupies one position and is insufficient for two nonempty parts.
example : ¬ MultiwayPartitionFeasible ([0], 2) := by
  rintro ⟨assign, _, _, _, onto, _, _⟩
  obtain ⟨j₀, hj₀, h₀⟩ := onto 0 (by decide)
  obtain ⟨j₁, hj₁, h₁⟩ := onto 1 (by decide)
  change j₀ < 1 at hj₀
  change j₁ < 1 at hj₁
  rw [show j₀ = 0 by omega] at h₀
  rw [show j₁ = 0 by omega] at h₁
  omega

example : ¬ MultiwayPartitionFeasible ([], 0) := by
  rintro ⟨_, _, h, _, _, _, _⟩
  exact Nat.lt_irrefl 0 h

example : multiwayPartitionDec [] = false := by
  have hd : bitDecode (α := MultiwayPartitionInstance) [] = none := by decide
  simp only [multiwayPartitionDec, hd]

-- The noncanonical one-bit payload [false] decodes to 2.
example : multiwayPartitionDec (delimit (delimit [false]) ++ [true]) = true := by
  have hd : bitDecode (α := MultiwayPartitionInstance)
      (delimit (delimit [false]) ++ [true]) = some ([2], 1) := by decide
  simp only [multiwayPartitionDec, hd, decide_eq_true_eq]
  refine ⟨[0], rfl, by decide, ?_, ?_, 2, ?_⟩
  · intro j hj
    change j < 1 at hj
    interval_cases j
    decide
  · intro p hp
    change p < 1 at hp
    interval_cases p
    exact ⟨0, by decide, rfl⟩
  · intro p hp
    change p < 1 at hp
    interval_cases p
    decide

end MetaMathlibExt.Complexity.NPComplete.MultiwayPartition.Tests
