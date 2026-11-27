/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterPMResidueArmLeg

namespace MetaMathlibExt

-- The allowable parts up to 5 are 1, 3 and 5. After taking one 5, choose two with repetition.
example : perimeterPMResidueArmLegCount 1 1 5 3 = 6 := by
  have h := perimeterPMResidueArmLegCount_ne_zero_iff_and_eq_choose
    (d := 1) (a := 1) (m := 5) (k := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact (h.2.1 (by decide) (by decide)).trans (by decide)

-- The negative residue introduces a fourth allowable part, so the binomial count changes.
example : perimeterPMResidueArmLegCount 1 1 7 3 = 10 := by
  have h := perimeterPMResidueArmLegCount_ne_zero_iff_and_eq_choose
    (d := 1) (a := 1) (m := 7) (k := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact (h.2.2 (by decide) (by decide)).trans (by decide)

-- Direct enumeration checks the minimum allowable part and a one-part negative-residue partition.
example : perimeterPMResidueArmLegCount 2 2 2 3 = 1 ∧
    perimeterPMResidueArmLegCount 2 2 3 1 = 1 := by
  decide

-- Modulo 5, the largest part 1 is below the minimum, and 4 lies outside the two classes.
example : perimeterPMResidueArmLegCount 2 2 1 2 = 0 ∧
    perimeterPMResidueArmLegCount 2 2 4 2 = 0 := by
  decide

end MetaMathlibExt
