/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.ZMod.Basic
import MathlibExt.Combinatorics.Enumerative.Partition.Counting
import MathlibExt.Combinatorics.Enumerative.Partition.RegularPartitionsLK

namespace MetaMathlibExt.regularPartitionCount_two_prime_mod_two

example : regularPartitionCount 2 5 0 = 1 := by decide

-- The single-part partition of 5 is allowed for (2, 7) and excluded for (2, 5).
example : regularPartitionCount 2 5 5 < regularPartitionCount 2 7 5 := by
  unfold regularPartitionCount
  apply Finset.card_lt_card
  have hsub : (Finset.univ : Finset (Nat.Partition 5)).filter
      (fun part => ∀ i ∈ part.parts, ¬ 2 ∣ i ∧ ¬ 5 ∣ i) ⊆
      Finset.univ.filter (fun part => ∀ i ∈ part.parts, ¬ 2 ∣ i ∧ ¬ 7 ∣ i) := by
    intro part hpart
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpart ⊢
    intro i hi
    have hi_le := Nat.Partition.le_of_mem_parts hi
    exact ⟨(hpart i hi).1, fun hd =>
      (by omega : ¬ 7 ≤ i) (Nat.le_of_dvd (part.parts_pos hi) hd)⟩
  refine (Finset.ssubset_iff_of_subset hsub).mpr ⟨Nat.Partition.indiscrete 5, ?_, ?_⟩ <;> simp

private lemma nonresidue_five_three : ¬ IsSquare ((24 * 3 + 1 : ℕ) : ZMod 5) := by
  change ¬ ∃ a : ZMod 5, (3 : ZMod 5) = a * a
  decide

example (n : ℕ) : regularPartitionCount 2 5 (5 * n + 3) ≡ 0 [MOD 2] :=
  regularPartitionCount_two_prime_mod_two (p := 5) (r := 3)
    (by decide) (by decide) nonresidue_five_three n

-- At `n = 0` the progression gives `b_{2,5}(3) = 2`: the partitions `3` and `1 + 1 + 1` count,
-- while `2 + 1` has the even part `2`. `decide` cannot list the partitions of `3`, so their
-- number comes from the part-counting recurrence `Nat.Partition.mul_card_eq_sum`.
example : regularPartitionCount 2 5 3 = 2 := by
  let p3 : Nat.Partition 3 := ⟨{3}, by simp, by decide⟩
  let p21 : Nat.Partition 3 := ⟨{2, 1}, by simp, by decide⟩
  let p111 : Nat.Partition 3 := ⟨{1, 1, 1}, by simp, by decide⟩
  have hne : p3 ≠ p21 ∧ p3 ≠ p111 ∧ p21 ≠ p111 := by decide +revert
  have h2 := Nat.Partition.mul_card_eq_sum 2
  have h3 := Nat.Partition.mul_card_eq_sum 3
  simp [show Finset.Icc 1 2 = {1, 2} by decide, show Finset.Icc 1 3 = {1, 2, 3} by decide] at h2 h3
  have hU : ({p3, p21, p111} : Finset (Nat.Partition 3)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, Finset.card_insert_of_notMem (by simp [hne.1, hne.2.1]),
      Finset.card_pair hne.2.2]
    omega
  unfold regularPartitionCount
  rw [← hU]
  dsimp only [p3, p21, p111]
  decide

end MetaMathlibExt.regularPartitionCount_two_prime_mod_two

namespace MetaMathlibExt

-- Here 8r + 1 is a nonsquare but 24r + 1 is a square modulo 5.
example (n : ℕ) : regularPartitionCount 4 5 (5 * n + 2) ≡ 0 [MOD 2] :=
  regularPartitionCount_four_prime_mod_two (p := 5) (r := 2) (by decide) (by decide)
    (by
      change ¬ ∃ a : ZMod 5, (2 : ZMod 5) = a * a
      decide) n

-- The representative r need not be less than p.
example (n : ℕ) : regularPartitionCount 4 7 (7 * n + 9) ≡ 0 [MOD 2] :=
  regularPartitionCount_four_prime_mod_two (p := 7) (r := 9) (by decide) (by decide)
    (by
      change ¬ ∃ a : ZMod 7, (3 : ZMod 7) = a * a
      decide) n

end MetaMathlibExt
