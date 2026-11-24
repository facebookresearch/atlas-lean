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
