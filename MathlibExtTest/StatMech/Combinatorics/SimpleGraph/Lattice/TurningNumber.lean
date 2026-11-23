/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CornerBalance

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber`

The rotation `rotPow` is evaluated on `(1, 0)`. The orbit results are instantiated on the boundary
orbit of the single cell `unitCell = {(0, 0)}` starting from the east-pointing dart `ucBase`
(witnesses from `MathlibExt.Combinatorics.SimpleGraph.Lattice.CornerBalance`): the predicate
`TurningIsFullRevolution` holds there (the orbit turns `-4` quarter turns over its period `4`), so
`orbitPeriod_ge_four_of_fullRevolution` is non-vacuous; `four_dvd_orbit_totalTurnZ` and
`abs_orbit_totalTurnZ_le` are applied to the same orbit and checked against the computed values.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber

open _root_.StatMech _root_.StatMech.Lattice

-- A quarter turn sends east `(1, 0)` to north `(0, 1)`.
example : rotPow 1 ![1, 0] = ![0, 1] := by
  rw [rotPow_one, rot90Fun_apply]; simp

-- A half turn negates.
example : rotPow 2 ![1, 0] = ![-1, 0] := by
  rw [rotPow_two]; funext i; fin_cases i <;> rfl

-- Three quarter turns send east to south.
example : rotPow 3 ![1, 0] = ![0, -1] := by
  rw [rotPow_three, rot90Fun_apply]; funext i; fin_cases i <;> rfl

-- `rotPow` adds exponents: `1 + 3 = 0` in `ZMod 4`.
example (x : Site 2) : rotPow 1 (rotPow 3 x) = x := by
  rw [← rotPow_add]; exact rotPow_zero x

-- The signed turn of the east-pointing boundary dart of the unit cell is a right turn.
example : turnZ unitCell ucDart0 = -1 := ucDart0_turnZ

-- The boundary orbit of the unit cell has period `4` and total turning `-4`.
example : totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 := by
  rw [unitCell_orbitPeriod_eq_four]; exact unitCell_totalTurnZ_four

-- `TurningIsFullRevolution` holds in a nontrivial case.
example : TurningIsFullRevolution unitCell ucBase := unitCell_turningIsFullRevolution

-- Non-vacuity of `orbitPeriod_ge_four_of_fullRevolution`.
example : 4 ≤ dartOrbitPeriod unitCell ucBase :=
  orbitPeriod_ge_four_of_fullRevolution unitCell ucBase unitCell_turningIsFullRevolution

-- `four_dvd_orbit_totalTurnZ` on the unit cell, consistent with the computed value `-4`.
example : (4 : ℤ) ∣ totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) :=
  four_dvd_orbit_totalTurnZ unitCell ucBase

-- `abs_orbit_totalTurnZ_le` on the unit cell is tight: `|-4| ≤ 4`.
example : |totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase)|
    ≤ (dartOrbitPeriod unitCell ucBase : ℤ) :=
  abs_orbit_totalTurnZ_le unitCell ucBase

-- `dir_iterate_eq_rotPow_cumTurn` after a full period recovers the initial direction.
example : ((dartNext unitCell)^[dartOrbitPeriod unitCell ucBase] ucBase.1).dir = ucBase.1.dir := by
  rw [orbit_iterate_period_eq]

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber
