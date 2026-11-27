/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterAlderIdentity

namespace MetaMathlibExt

-- Both classes are empty below the smallest allowed part, including at a = d + 1.
example : perimeterDistinctCount 2 3 2 = 0 ∧ perimeterResidueCount 2 3 2 = 0 := by
  decide

-- At the smallest allowed perimeter, each side consists only of the singleton partition.
example : perimeterDistinctCount 2 3 3 = 1 ∧ perimeterResidueCount 2 3 3 = 1 := by
  decide

-- At the first perimeter admitting a two-part 2-distinct partition with minimum part 2,
-- the two sides count different partitions: {5}, {4, 2} and {5}, {2, 2, 2, 2}.
example : perimeterDistinctCount 2 2 5 = 2 ∧ perimeterResidueCount 2 2 5 = 2 := by
  decide

-- At perimeter 6, the supported indices are 0, 1 and 2, giving counts 1 + 4 + 3.
example : perimeterDistinctCount 1 1 6 = 8 ∧ perimeterResidueCount 1 1 6 = 8 := by
  decide

example {d a n : ℕ} (hd : 0 < d) (hn : 0 < n) (ha : 1 ≤ a) (had : a ≤ d + 1) :
    perimeterDistinctCount d a n = perimeterResidueCount d a n :=
  perimeterDistinctCount_eq_perimeterResidueCount (hd := hd) (hn := hn) (ha := ha) (had := had)

end MetaMathlibExt
