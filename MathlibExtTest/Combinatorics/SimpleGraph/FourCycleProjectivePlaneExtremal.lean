/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.FourCycleProjectivePlaneExtremal

open SimpleGraph
open MathlibExt.Combinatorics.SimpleGraph.FourCycleExtremalValuesWanted

-- The first eligible power of two.
example : extremalNumber 273 (cycleGraph 4) = 2312 :=
  extremalNumber_cycleGraph_four_projectivePlane_order 16
    (hq := (isPrimePow_nat_iff 16).mpr ⟨2, 4, by decide, by decide, by decide⟩)
    (h13 := by decide)

example : extremalNumber 307 (cycleGraph 4) = 2754 :=
  extremalNumber_cycleGraph_four_projectivePlane_order 17
    (hq := Nat.Prime.isPrimePow (by decide)) (h13 := by decide)
