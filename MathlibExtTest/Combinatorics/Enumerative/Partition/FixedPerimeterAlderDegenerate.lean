/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterAlderDegenerate

open MetaMathlibExt

-- Apply the public theorem at the least odd gap and the least positive perimeter.
example : perimeterPMResidueCount 1 2 1 ≤ perimeterDistinctCount 1 2 1 :=
  perimeterPMResidueCount_le_perimeterDistinctCount_of_odd (d := 1) (n := 1)
    (hn := by decide) (hd := by decide)

-- The residues coincide: the single partition {2} is counted only once.
example : perimeterPMResidueCount 1 2 2 = 1 ∧ perimeterDistinctCount 1 2 2 = 1 := by
  decide

-- At perimeter 4, {4} and {3, 2} are distinct, but only {2, 2, 2} meets the residue condition.
example : perimeterPMResidueCount 1 2 4 = 1 ∧ perimeterDistinctCount 1 2 4 = 2 := by
  decide
