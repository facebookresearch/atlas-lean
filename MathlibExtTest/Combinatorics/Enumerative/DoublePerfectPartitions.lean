/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.DoublePerfectPartitions

namespace MetaMathlibExt

-- At the lower bound, the two subpartitions of 2 are {2} and {1, 1}.
private theorem order_one_four : IsDoublePerfectOfOrder 1 4 {1, 1, 2} := by
  unfold IsDoublePerfectOfOrder subpartitionCount
  decide

example (m : ℕ) : IsDoublePerfectOfOrder 1 (4 + m * 3)
    ({1, 1, 2} + Multiset.replicate m 3) :=
  isDoublePerfectOfOrder_add_replicate 1 4 (by decide) (by decide) _ order_one_four m

-- With two new threes, 6 has two representations and 9 has only one.
example : subpartitionCount {1, 1, 2, 3, 3} 6 = 2 ∧ subpartitionCount {1, 1, 2, 3, 3} 9 = 1 := by
  decide

-- Below the bound, inserting two copies can destroy double perfection.
example : IsDoublePerfectOfOrder 1 2 {1, 1} ∧ ¬ IsDoublePerfectOfOrder 1 4 {1, 1, 1, 1} := by
  unfold IsDoublePerfectOfOrder subpartitionCount
  decide

-- The empty factorization gives the empty perfect partition of zero.
example : IsPerfectPartition 0 (perfectPartitionOfFactorization []) := by
  unfold IsPerfectPartition subpartitionCount
  decide

-- The first excluded positive multiplicity is three.
example : ¬ ∃ n : ℕ, ∃ p : n.Partition, ∃ m,
    3 ≤ m ∧ m ≤ n - 3 ∧ subpartitionCount p.parts m = 3 ∧
      ∀ k, 0 < k → k < n → k ≠ m → subpartitionCount p.parts k = 1 := by
  intro h
  have := (exists_partition_unique_subsums_but_one_iff 3 (by decide)).mp h
  omega

-- With zero multiplicity, the partition (2) misses its only interior sum.
example : ∃ p : Nat.Partition 2, subpartitionCount p.parts 1 = 0 ∧
    ∀ k, 0 < k → k < 2 → k ≠ 1 → subpartitionCount p.parts k = 1 := by
  refine ⟨Nat.Partition.indiscrete 2, by decide, ?_⟩
  omega

-- Both shapes can describe the same partition, using different factorizations of four.
example : IsTypeADoublePerfect 1 5 {1, 1, 1, 2} ∧
    ({1, 1, 1, 2} : Multiset ℕ) =
      Multiset.replicate 2 1 + perfectPartitionOfFactorization [2, 2] ∧
    ({1, 1, 1, 2} : Multiset ℕ) = perfectPartitionOfFactorization [4] + {2} := by
  refine ⟨⟨?_, {1, 2}, ?_, Or.inl ?_⟩, ?_⟩
  · unfold IsDoublePerfectOfOrder subpartitionCount
    decide
  · unfold IsPerfectPartition subpartitionCount
    decide
  · decide
  · decide

-- At the lower bound for order two, three cannot be the first factor of four.
example : ∃ as : List ℕ, (∀ a ∈ as, 2 ≤ a) ∧ as.prod = 4 ∧ as.head? ≠ some 3 ∧
    ({1, 1, 1, 3} : Multiset ℕ) = perfectPartitionOfFactorization as + {3} := by
  have hl : IsTypeADoublePerfect 2 6 {1, 1, 1, 3} := by
    refine ⟨?_, {1, 1, 1}, ?_, Or.inr ?_⟩
    · unfold IsDoublePerfectOfOrder subpartitionCount
      decide
    · unfold IsPerfectPartition subpartitionCount
      decide
    · decide
  rcases typeADoublePerfect_forms 2 6 (by decide) (by decide) _ hl with h | h
  · obtain ⟨as, _, hprod, _⟩ := h
    omega
  · exact h

end MetaMathlibExt
