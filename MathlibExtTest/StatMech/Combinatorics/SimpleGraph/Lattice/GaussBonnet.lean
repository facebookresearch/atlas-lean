/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.GaussBonnet
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.GaussBonnet`

* `unitCell_eulerCharOne`, `domino_eulerCharOne`.
* `gaussBonnet_local_global` and `turningIsFullRevolution_iff_revCount` on the unit cell, giving
  `revCount = ±1` there.
* `cycleGraph_cyclomaticNumber_eq_one` for `C_4`.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.GaussBonnet

example : EulerCharOne unitCell ucBase := unitCell_eulerCharOne

example : EulerCharOne domino dmBase := domino_eulerCharOne

example : totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) =
    4 * revCount unitCell ucBase := gaussBonnet_local_global unitCell ucBase

example : cyclomaticNumber (SimpleGraph.cycleGraph (1 + 3)) = 1 := cycleGraph_cyclomaticNumber_eq_one 1

example : revCount unitCell ucBase = 1 ∨ revCount unitCell ucBase = -1 :=
  (turningIsFullRevolution_iff_revCount _ _).mp
    ((eulerCharOne_iff_turningIsFullRevolution _ _
      (by rw [unitCell_orbitPeriod_eq_four]; norm_num)).mp unitCell_eulerCharOne)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.GaussBonnet
