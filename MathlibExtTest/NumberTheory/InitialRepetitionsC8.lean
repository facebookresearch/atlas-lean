/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.IsSquare
import MathlibExt.NumberTheory.InitialRepetitionsC8
import MathlibExt.Combinatorics.Enumerative.Partition.Counting

/-! # Tests for the initial-repetitions partition function `c₈` -/

open MetaMathlibExt Finset

-- The empty partition lies in the distinct even parts case.
example : initialRepetitionsC8 0 = 1 := by
  simp [initialRepetitionsC8, univ_unique]

-- With largest odd part one, two copies of one are allowed. The other partition is the single two.
example : initialRepetitionsC8 2 = 2 := by
  let double : Nat.Partition 2 := ⟨{1, 1}, by simp, by decide⟩
  let single : Nat.Partition 2 := ⟨{2}, by simp, by decide⟩
  have hne : double ≠ single := by decide +revert
  have hcard := Nat.Partition.mul_card_eq_sum 2
  simp [show Icc 1 2 = {1, 2} by decide] at hcard
  have hU : ({double, single} : Finset (Nat.Partition 2)) = univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    simp [hne]
    omega
  unfold initialRepetitionsC8
  rw [← hU]
  dsimp only [double, single]
  decide

-- The least allowed prime has a nonempty progression since 15 · 2 + 1 is 3 modulo 7.
example (n : ℕ) : Even (initialRepetitionsC8 (7 * n + 2)) :=
  initialRepetitionsC8_prime_mul_add_even 7 2 n (by decide) (by decide) (by decide)
    (by unfold IsSquare; decide)

-- At residue 6 the discriminant vanishes modulo 7, so it counts as a square.
example : IsSquare ((15 * 6 + 1 : ℕ) : ZMod 7) := ⟨0, by decide⟩

-- The same discriminant, 91, is a nonsquare in ℕ, so the general theorem still applies.
example : Even (initialRepetitionsC8 6) :=
  initialRepetitionsC8_even_of_not_isSquare 6 (by norm_num)
