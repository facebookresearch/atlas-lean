/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.StanleyElderParts

namespace MetaMathlibExt

-- The empty partition contributes nothing to either total.
example : (∑ p : Nat.Partition 0, p.parts.count 1) = 0 ∧
    (∑ p : Nat.Partition 0, p.parts.toFinset.card) = 0 := by
  have h : (∑ p : Nat.Partition 0, p.parts.count 1) = 0 := by simp
  exact ⟨h, (sum_count_one_eq_sum_card_toFinset 0).symm.trans h⟩

-- The partition 1+1+1+1 alone contributes four to the total number of ones.
example : 4 ≤ (∑ p : Nat.Partition 4, p.parts.count 1) ∧
    4 ≤ (∑ p : Nat.Partition 4, p.parts.toFinset.card) := by
  let p : Nat.Partition 4 := ⟨{1, 1, 1, 1}, by simp, by decide⟩
  have hp : p.parts.count 1 = 4 := by decide +kernel
  have h : 4 ≤ ∑ q : Nat.Partition 4, q.parts.count 1 :=
    hp ▸ Finset.single_le_sum (f := fun q : Nat.Partition 4 => q.parts.count 1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)
  exact ⟨h, (sum_count_one_eq_sum_card_toFinset 4) ▸ h⟩

end MetaMathlibExt

namespace MetaMathlibExt.nColor_evenParts_generatingFunction

-- The empty partition contributes no even parts.
example : (∑ s ∈ nColorPartitions 0, (s.filter fun p => Even p.1).card) = 0 := by
  decide

-- At size two there is one occurrence of each color.
example : (∑ s ∈ nColorPartitions 2, (s.filter fun p => Even p.1).card) = 2 := by
  decide +kernel

-- At size four, the shapes 4, 2+2 and 2+1+1 contribute 4, 6 and 2 occurrences.
example : (∑ s ∈ nColorPartitions 4, (s.filter fun p => Even p.1).card) = 12 := by
  decide +kernel

end MetaMathlibExt.nColor_evenParts_generatingFunction

namespace MetaMathlibExt.nColor_partsMultiplicityGe_generatingFunction

-- A partition of one cannot contain two copies of any colored part.
example : (∑ s ∈ nColorPartitions 1, (s.toFinset.filter fun p => 2 ≤ s.count p).card) = 0 := by
  decide

-- Three partitions of four contain at least two ones, including the partition with four ones.
-- Two more contain a repeated two of one color. A pair of different colors does not qualify.
example : (∑ s ∈ nColorPartitions 4, (s.toFinset.filter fun p => 2 ≤ s.count p).card) = 5 := by
  decide +kernel

end MetaMathlibExt.nColor_partsMultiplicityGe_generatingFunction
