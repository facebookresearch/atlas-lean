/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.InitialRepetitionsC8Prime
import MathlibExt.Combinatorics.Enumerative.Partition.Counting

/-! # Tests for partitions with a possibly distinguished even part -/

open MetaMathlibExt Finset

-- Only the unmarked empty partition contributes.
example : initialRepetitionsC8Prime 0 = 1 := by
  simp [initialRepetitionsC8Prime, univ_unique]

-- The partition consisting of a single two occurs twice, with and without a mark.
example : initialRepetitionsC8Prime 2 = 2 := by
  let double : Nat.Partition 2 := ⟨{1, 1}, by simp, by decide⟩
  let single : Nat.Partition 2 := ⟨{2}, by simp, by decide⟩
  have hne : double ≠ single := by decide +revert
  have hcard := Nat.Partition.mul_card_eq_sum 2
  simp [show Icc 1 2 = {1, 2} by decide] at hcard
  have hU : ({double, single} : Finset (Nat.Partition 2)) = univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    simp [hne]
    omega
  unfold initialRepetitionsC8Prime
  rw [← hU]
  dsimp only [double, single]
  decide

-- At the least allowed prime, 19 is congruent to the nonresidue 5.
example (n : ℕ) : Even (initialRepetitionsC8Prime (7 * n + 1)) :=
  initialRepetitionsC8Prime_prime_mul_add_even 7 1 n (by decide) (by decide) (by decide)
    (by unfold IsSquare; decide)

-- The discriminant at residue three is zero modulo seven and hence a square.
example : IsSquare ((15 * 3 + 4 : ℕ) : ZMod 7) := ⟨0, by decide⟩
