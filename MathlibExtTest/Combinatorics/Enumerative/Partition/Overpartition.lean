/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition

namespace Nat.Overpartition

example : Nat.Overpartition 0 :=
  ofPartition (Nat.Partition.ofMultiset (∅ : Multiset ℕ))

private def partition14 : Nat.Partition 14 :=
  Nat.Partition.ofMultiset {5, 5, 3, 1}

private def overpartition14 : Nat.Overpartition 14 where
  toPartition := partition14
  overlines := {5, 1}
  overlines_subset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · show (5 : ℕ) ∈ partition14.parts.toFinset
      rw [Multiset.mem_toFinset]
      decide
    · show (1 : ℕ) ∈ partition14.parts.toFinset
      rw [Multiset.mem_toFinset]
      decide

-- Selective overlining, membership, positivity, and the `full` constructor.
example :
    overpartition14.IsOverlined 5 ∧ overpartition14.IsOverlined 1 ∧
      ¬overpartition14.IsOverlined 3 ∧ 5 ∈ overpartition14.toPartition.parts ∧
        (0 : ℕ) < 5 ∧ (full partition14).IsOverlined 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [overpartition14, IsOverlined]
  · simp [overpartition14, IsOverlined]
  · simp [overpartition14, IsOverlined]
  · decide
  · exact overpartition14.isOverlined_pos (by simp [overpartition14, IsOverlined])
  · exact (isOverlined_full partition14 3).mpr (by decide)

-- Empty and full constructors have the expected underlying partition and overline sets.
example : (ofPartition partition14).overlines = ∅ := by
  simp

example : (full partition14).overlines = partition14.parts.toFinset := by
  simp

example (a : ℕ) : ¬ (ofPartition partition14).IsOverlined a := by
  simp

-- Zero boundary: the unique overpartition of `0` has empty overlines and any two coincide.
example (O : Nat.Overpartition 0) : O.overlines = ∅ :=
  overlines_eq_empty_of_zero

example (O₁ O₂ : Nat.Overpartition 0) : O₁ = O₂ :=
  eq_of_zero O₁ O₂

-- Finiteness: the `Fintype` instance enumerates `Overpartition n`; there is `1` overpartition
-- of `0` and there are `2` of `1` (`1̄` and `1`), OEIS A015128.
example : Fintype.card (Nat.Overpartition 0) = 1 := by decide
example : Fintype.card (Nat.Overpartition 1) = 2 := by decide

end Nat.Overpartition
