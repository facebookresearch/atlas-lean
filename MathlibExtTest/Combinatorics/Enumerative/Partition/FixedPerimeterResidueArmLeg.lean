/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterResidueArmLeg

namespace MetaMathlibExt

-- The zero residue modulo 2 allows 2, 4 and 6. Removing a 6 leaves two parts.
example : perimeterResidueArmLegCount 1 2 6 3 = 6 := by
  have h := perimeterResidueArmLegCount_ne_zero_iff_and_eq_choose
    (d := 1) (a := 2) (m := 6) (k := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact (h.2 (by decide) (by decide)).trans (by decide)

-- Direct enumeration at the least positive representative and at length one.
example : perimeterResidueArmLegCount 2 3 3 3 = 1 ∧ perimeterResidueArmLegCount 2 3 6 1 = 1 := by
  decide

-- A smaller maximum and a larger maximum in the wrong residue class are both impossible.
example : perimeterResidueArmLegCount 2 2 1 2 = 0 ∧ perimeterResidueArmLegCount 2 2 3 2 = 0 := by
  decide

end MetaMathlibExt
