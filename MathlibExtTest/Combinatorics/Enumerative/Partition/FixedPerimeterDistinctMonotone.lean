/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterDistinctMonotone

namespace MetaMathlibExt

-- At the smallest positive perimeter, only the minimum-part bound is strict.
example : perimeterDistinctCount 1 2 1 = 0 ∧ perimeterDistinctCount 2 1 1 = 1 ∧
    perimeterDistinctCount 1 1 1 = 1 ∧ perimeterDistinctCount 1 1 2 = 1 := by
  decide

-- At perimeter three, each of the three inequalities can be strict.
example : perimeterDistinctCount 1 2 3 < perimeterDistinctCount 1 1 3 ∧
    perimeterDistinctCount 2 1 3 < perimeterDistinctCount 1 1 3 ∧
    perimeterDistinctCount 1 1 3 < perimeterDistinctCount 1 1 4 := by
  decide

example : perimeterDistinctCount 1 2 3 ≤ perimeterDistinctCount 1 1 3 ∧
    perimeterDistinctCount 2 1 3 ≤ perimeterDistinctCount 1 1 3 ∧
    perimeterDistinctCount 1 1 3 ≤ perimeterDistinctCount 1 1 4 :=
  perimeterDistinctCount_shift_inequalities (d := 1) (a := 1) (n := 3)
    (hd := by decide) (hn := by decide) (ha := by decide)

end MetaMathlibExt
