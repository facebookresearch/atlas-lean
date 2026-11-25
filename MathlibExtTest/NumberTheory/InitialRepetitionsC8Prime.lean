/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.InitialRepetitionsC8Prime
import MathlibExt.Combinatorics.Enumerative.Partition.Counting

/-! # Tests for the partition function `c₈'` with a possibly distinguished part -/

open MetaMathlibExt Finset

-- The least allowed prime: 15 · 1 + 4 = 19 is 5 modulo 7, a nonsquare.
example (n : ℕ) : Even (initialRepetitionsC8Prime (7 * n + 1)) :=
  initialRepetitionsC8Prime_prime_mul_add_even 7 1 n (by decide) (by decide) (by decide)
    (by unfold IsSquare; decide)

-- With `n = 0` the theorem gives the parity of one value: 15 · 5 + 4 = 79 is 2 modulo 11.
example : Even (initialRepetitionsC8Prime 5) :=
  initialRepetitionsC8Prime_prime_mul_add_even 11 5 0 (by decide) (by decide) (by decide)
    (by unfold IsSquare; decide)

-- At residue 3 the value 15 · 3 + 4 = 49 vanishes modulo 7, so it counts as a square.
example : IsSquare ((15 * 3 + 4 : ℕ) : ZMod 7) := ⟨0, by decide⟩

-- The hypothesis cannot be dropped: `c₈'(3) = 1` is odd. The only partition counted is `2 + 1`,
-- with `m = 1`; neither `3` nor `1 + 1 + 1` qualifies.
example : initialRepetitionsC8Prime 3 = 1 := by
  let p3 : Nat.Partition 3 := ⟨{3}, by simp, by decide⟩
  let p21 : Nat.Partition 3 := ⟨{2, 1}, by simp, by decide⟩
  let p111 : Nat.Partition 3 := ⟨{1, 1, 1}, by simp, by decide⟩
  have hne : p3 ≠ p21 ∧ p3 ≠ p111 ∧ p21 ≠ p111 := by decide +revert
  have h2 := Nat.Partition.mul_card_eq_sum 2
  have h3 := Nat.Partition.mul_card_eq_sum 3
  simp [show Icc 1 2 = {1, 2} by decide, show Icc 1 3 = {1, 2, 3} by decide] at h2 h3
  have hU : ({p3, p21, p111} : Finset (Nat.Partition 3)) = univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    rw [card_univ, card_insert_of_notMem (by simp [hne.1, hne.2.1]), card_pair hne.2.2]
    omega
  unfold initialRepetitionsC8Prime
  rw [← hU]
  dsimp only [p3, p21, p111]
  decide
