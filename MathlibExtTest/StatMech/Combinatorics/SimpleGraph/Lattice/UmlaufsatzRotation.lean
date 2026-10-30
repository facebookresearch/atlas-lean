/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.UmlaufsatzRotation
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.UmlaufsatzRotation`

* `uc_unitCell_totalTurnAngle_eq_two_pi`, `uc_verticalDomino_eulerCharOne`.
* `uc_winds_iff` on the unit cell: both winding bounds hold (total turn `-4`).
* `uc_totalTurnZ_rot`: rotation invariance on the unit cell.
* The vacuous headlines (`uc_turningIsFullRevolution`, `uc_totalTurn_eq_four`, ...) are not
  instantiated: their hypothesis is refuted (`not_bpc_BalanceSaturatingContraction`).
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.UmlaufsatzRotation

example : totalTurnAngle unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 2 * Real.pi ∨
    totalTurnAngle unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -(2 * Real.pi) :=
  uc_unitCell_totalTurnAngle_eq_two_pi

example : EulerCharOne (uc_rotSet domino) (uc_rotSub domino dmBase) :=
  uc_verticalDomino_eulerCharOne

example : uc_WindsAtMostOnce unitCell ucBase ∧ uc_WindsAtLeastOnce unitCell ucBase := by
  rw [uc_winds_iff, ← cornerBalance_eq_totalTurnZ, unitCell_cornerBalance ucBase (Or.inl rfl)]
  simp

example : totalTurnZ (uc_rotSet unitCell) (uc_rotSub unitCell ucBase).1
    (dartOrbitPeriod (uc_rotSet unitCell) (uc_rotSub unitCell ucBase)) = -4 := by
  rw [uc_totalTurnZ_rot, ← cornerBalance_eq_totalTurnZ, unitCell_cornerBalance ucBase (Or.inl rfl)]

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.UmlaufsatzRotation
