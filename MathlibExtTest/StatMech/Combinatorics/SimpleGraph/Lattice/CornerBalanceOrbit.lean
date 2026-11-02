/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CornerBalanceOrbit
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.CornerBalanceOrbit`

* `BalanceIsFour` holds for every boundary orbit of a one-site set (from
  `singleton_cornerBalance`), and `balanceIsFour_iff_revCount_pm_one` turns it into
  `revCount = ±1`.
* `cornerBalance_eq_four_revCount` on the unit cell: `revCount = -1`.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.CornerBalanceOrbit

theorem singleton_balanceIsFour (a : {e : Dart // IsBoundaryDart ({0} : Set (Site 2)) e}) :
    BalanceIsFour ({0} : Set (Site 2)) a := Or.inr (singleton_cornerBalance 0 a)

example (a : {e : Dart // IsBoundaryDart ({0} : Set (Site 2)) e}) :
    revCount ({0} : Set (Site 2)) a = 1 ∨ revCount ({0} : Set (Site 2)) a = -1 :=
  (balanceIsFour_iff_revCount_pm_one _ a).mp (singleton_balanceIsFour a)

example : revCount unitCell ucBase = -1 := by
  have h := cornerBalance_eq_four_revCount unitCell ucBase
  rw [unitCell_cornerBalance ucBase (Or.inl rfl)] at h
  omega

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.CornerBalanceOrbit
