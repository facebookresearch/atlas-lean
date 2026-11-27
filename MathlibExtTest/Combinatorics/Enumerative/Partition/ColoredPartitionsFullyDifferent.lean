/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.ColoredPartitionsFullyDifferent

namespace MetaMathlibExt.card_coloredPartitions_fullyDifferent

-- The empty set gives one coloring of the empty partition.
example :
    (∑ μ ∈ Nat.Partition.distincts 0,
      ((μ.parts.sort (· ≤ ·)).mapIdx fun i q => q - i).prod) = 1 := by
  rw [← card_coloredPartitions_fullyDifferent]
  decide

-- There are four singleton colorings and two colorings of 1 + 3.
-- The candidate {(2, 1), (2, 2)} is excluded by the distinct-size condition.
set_option maxRecDepth 4096 in
example :
    (∑ μ ∈ Nat.Partition.distincts 4,
      ((μ.parts.sort (· ≤ ·)).mapIdx fun i q => q - i).prod) = 6 := by
  rw [← card_coloredPartitions_fullyDifferent]
  decide

end MetaMathlibExt.card_coloredPartitions_fullyDifferent

namespace MetaMathlibExt.card_coloredPartitions_fullyDifferent_le

private def boundedCount (n : ℕ) : ℕ :=
  (((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p : ℕ × ℕ => p.2 ≤ p.1)).powerset.filter
    (fun T => T.Nonempty ∧ (T.image Prod.fst).card = T.card ∧
      (T.image Prod.snd).card = T.card)).card

-- The empty placement is excluded, even when the board is empty.
example : boundedCount 0 = 0 :=
  (card_coloredPartitions_fullyDifferent_le (n := 0)).trans (by decide +kernel)

example : boundedCount 2 = 4 :=
  (card_coloredPartitions_fullyDifferent_le (n := 2)).trans (by decide +kernel)

example : boundedCount 3 = 14 :=
  (card_coloredPartitions_fullyDifferent_le (n := 3)).trans (by decide +kernel)

-- Independently enumerate the 3-row board: six singletons, seven pairs, and one triple.
set_option maxRecDepth 4096 in
example : boundedCount 3 = 14 := by decide

end MetaMathlibExt.card_coloredPartitions_fullyDifferent_le
