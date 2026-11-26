/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.InitialRepetitionsC3
import MathlibExt.Combinatorics.Enumerative.Partition.Counting

/-! # Tests for the initial-repetitions partition function $c_3$ -/

open MetaMathlibExt Finset

-- A positive square of compulsory ones rules out the empty partition.
example : initialRepetitionsC3 0 = 0 := by
  simp [initialRepetitionsC3]

-- The single part one is already sufficient for the index one.
example : initialRepetitionsC3 1 = 1 := by
  simp only [initialRepetitionsC3, univ_unique, filter_singleton]
  decide

-- Two ones are allowed for the index one. The partition consisting of a two is excluded.
example : initialRepetitionsC3 2 = 1 := by
  let double : Nat.Partition 2 := ⟨{1, 1}, by simp, by decide⟩
  let single : Nat.Partition 2 := ⟨{2}, by simp, by decide⟩
  have hne : double ≠ single := by decide +revert
  have hcard := Nat.Partition.mul_card_eq_sum 2
  simp [show Icc 1 2 = {1, 2} by decide] at hcard
  have hU : ({double, single} : Finset (Nat.Partition 2)) = univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    simp [hne]
    omega
  unfold initialRepetitionsC3
  rw [← hU]
  dsimp only [double, single]
  decide

-- At residue five, the two discriminants reduce to six and eight modulo eleven.
example (n : ℕ) : Even (initialRepetitionsC3 (11 * n + 5)) :=
  initialRepetitionsC3_prime_mul_add_even 11 5 n (hp := by decide) (hp5 := by decide)
    (hr := by decide) (h12 := by unfold IsSquare; decide) (h8 := by unfold IsSquare; decide)
