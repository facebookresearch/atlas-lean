/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.Counting
import MathlibExt.Combinatorics.Enumerative.Partition.RegularTripartitionCongruences

open MetaMathlibExt

-- Both divisors are attained at the first indices in the two progressions.
example : regularTripartitionCount 3 1 = 3 := regularTripartitionCount_one 3 (by decide)

example : regularTripartitionCount 3 2 = 9 := by
  have card (n : ℕ) (hn : n < 3) :
      (Nat.Partition.restricted n (¬ 3 ∣ ·)).card = Fintype.card (Nat.Partition n) := by
    unfold Nat.Partition.restricted
    rw [Finset.filter_true_of_mem, Finset.card_univ]
    intro p _ i hi hdiv
    exact hn.not_ge ((Nat.le_of_dvd (p.parts_pos hi) hdiv).trans (p.le_of_mem_parts hi))
  have h := Nat.Partition.mul_card_eq_sum 2
  simp [show Finset.Icc 1 2 = {1, 2} by decide] at h
  have h₂ : Fintype.card (Nat.Partition 2) = 2 := by omega
  simp [regularTripartitionCount, Finset.Nat.antidiagonal_succ, card 0 (by decide),
    card 1 (by decide), card 2 (by decide), h₂]

example : 3 ∣ regularTripartitionCount 3 4 ∧ 9 ∣ regularTripartitionCount 3 5 :=
  regularTripartitionCount_three_mod_three_nine (n := 1)

-- The empty triple is allowed even when every positive part is forbidden.
example : regularTripartitionCount 1 0 = 1 := regularTripartitionCount_zero 1

example : regularTripartitionCount 1 1 = 0 := by
  have h : Nat.Partition.restricted 1 (fun _ ↦ False) = ∅ := by
    ext p
    simp [Nat.Partition.restricted, Subsingleton.elim p default]
  simp [regularTripartitionCount, Finset.Nat.antidiagonal_succ, h]

-- The exceptional prime 3 gives an index congruent to 2 modulo 3.
example : 3 ∣ regularTripartitionCount 3 11 :=
  regularTripartitionCount_three_prime_three_mod_four 3 0 0 1
    (by decide) (by decide) (by decide) (by decide)

-- The upper endpoint i = p - 1 with a positive power parameter.
example : 3 ∣ regularTripartitionCount 3 13977 :=
  regularTripartitionCount_three_prime_three_mod_four 7 1 1 6
    (by decide) (by decide) (by decide) (by decide)
