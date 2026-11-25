/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterArmLegEquality

namespace MetaMathlibExt

-- The transformed largest part and length are both four.
example : perimeterDistinctArmLegCount 2 1 6 2 = 4 ∧ perimeterResidueArmLegCount 2 1 4 4 = 4 := by
  decide

-- At the least possible largest part, the transformed partition has exactly one part.
example : perimeterDistinctArmLegCount 2 1 3 2 = perimeterResidueArmLegCount 2 1 4 1 ∧
    perimeterResidueArmLegCount 2 1 4 1 = 1 := by
  exact ⟨perimeterDistinctArmLegCount_eq_perimeterResidueArmLegCount
    (d := 2) (a := 1) (m := 3) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide),
    by decide⟩

-- Just below the threshold, the transformed length truncates to zero.
example : perimeterDistinctArmLegCount 2 1 2 2 = perimeterResidueArmLegCount 2 1 4 0 ∧
    perimeterResidueArmLegCount 2 1 4 0 = 0 := by
  exact ⟨perimeterDistinctArmLegCount_eq_perimeterResidueArmLegCount
    (d := 2) (a := 1) (m := 2) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide),
    by decide⟩

end MetaMathlibExt
