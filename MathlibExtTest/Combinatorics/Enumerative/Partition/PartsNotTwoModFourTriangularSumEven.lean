/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.PartsNotTwoModFourTriangularSumEven

private def triangularSumP2 (n : ℕ) : ℕ :=
  ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
    MetaMathlibExt.partsNotTwoModFourCount (n - k * (k + 1) / 2)

example (n : ℕ) (hn : 0 < n) : Even (triangularSumP2 n) :=
  MetaMathlibExt.partsNotTwoModFour_triangular_sum_even (n := n) (hn := hn)

-- The count $P_2(0)$: only the empty partition counts.
example : MetaMathlibExt.partsNotTwoModFourCount 0 = 1 := by decide

-- The count $P_2(1)$: only the partition $1$ counts.
example : MetaMathlibExt.partsNotTwoModFourCount 1 = 1 := by
  unfold MetaMathlibExt.partsNotTwoModFourCount Nat.Partition.restricted
  simp

-- At zero the triangular sum is $1$, so positivity is necessary.
example : triangularSumP2 0 = 1 := by decide

namespace MetaMathlibExt.partsNotTwoModFour_triangular_sum_even

open Finset

-- Count the submultisets of a supply containing enough copies of each admissible part.
private theorem count_from_supply (n : ℕ) (s : Multiset ℕ)
    (hs : ∀ i ∈ Icc 1 n, i % 4 ≠ 2 → n / i ≤ s.count i) :
    partsNotTwoModFourCount n = (s.powerset.toFinset.filter fun m =>
      m.sum = n ∧ ∀ i ∈ m, 0 < i ∧ i % 4 ≠ 2).card := by
  unfold partsNotTwoModFourCount Nat.Partition.restricted
  apply Finset.card_bij (fun p _ => p.parts)
  · intro p hp
    have hmod := (Finset.mem_filter.mp hp).2
    refine Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr (Multiset.mem_powerset.mpr ?_),
      p.parts_sum, fun i hi => ⟨p.parts_pos hi, hmod i hi⟩⟩
    apply Multiset.le_iff_count.mpr
    intro i
    by_cases hi : i ∈ p.parts
    · obtain ⟨t, ht⟩ := exists_add_of_le (Multiset.le_count_iff_replicate_le.mp
        (le_rfl : p.parts.count i ≤ p.parts.count i))
      have hsum := congrArg Multiset.sum ht
      rw [p.parts_sum, Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul] at hsum
      have hbound : p.parts.count i * i ≤ n := (Nat.le_add_right _ _).trans_eq hsum.symm
      exact ((Nat.le_div_iff_mul_le (p.parts_pos hi)).mpr hbound).trans
        (hs i (mem_Icc.mpr ⟨p.parts_pos hi, p.le_of_mem_parts hi⟩) (hmod i hi))
    · simp [Multiset.count_eq_zero_of_notMem hi]
  · exact fun _ _ _ _ => Nat.Partition.ext
  · intro m hm
    obtain ⟨hsum, hparts⟩ := (Finset.mem_filter.mp hm).2
    exact ⟨⟨m, fun hi => (hparts _ hi).1, hsum⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => (hparts i hi).2⟩, rfl⟩

-- At two, only the partition 1 + 1 survives.
example : partsNotTwoModFourCount 2 = 1 := by
  rw [count_from_supply 2 {1, 1} (by decide)]
  decide +kernel

-- At six, both 2 and 6 are excluded, while repeated parts 1 and 3 are allowed.
set_option maxRecDepth 4096 in
example : partsNotTwoModFourCount 6 = 5 := by
  rw [count_from_supply 6 {1, 1, 1, 1, 1, 1, 3, 3, 4, 5} (by decide)]
  decide +kernel

end MetaMathlibExt.partsNotTwoModFour_triangular_sum_even
