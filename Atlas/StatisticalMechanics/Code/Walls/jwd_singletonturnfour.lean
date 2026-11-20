/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.TurningNumber
import Code.Lattice.CornerBalance
import Code.Lattice.EarContraction

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice




















theorem jwd_singleton_totalTurn (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}) :
    totalTurnZ ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) = -4 := by
  rw [← cornerBalance_eq_totalTurnZ]
  exact singleton_cornerBalance v a










theorem jwd_singleton_cornerBalance (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}) :
    cornerBalance ({v} : Set (Site 2)) a = -4 :=
  singleton_cornerBalance v a





theorem jwd_singleton_corner_counts (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}) :
    rightCornerCount ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) -
      leftCornerCount ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) = -4 := by
  have h := jwd_singleton_cornerBalance v a
  rwa [cornerBalance] at h









theorem jwd_singleton_eq_transUnitCell (v : Site 2) :
    ({v} : Set (Site 2)) = transSet v unitCell :=
  (transSet_unitCell v).symm









theorem jwd_singleton_totalTurn_reduce (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e})
    (b : {e : Dart // IsBoundaryDart unitCell e}) (he : a.1 = transDart v b.1) :
    totalTurnZ ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a)
      = totalTurnZ unitCell b.1 (dartOrbitPeriod unitCell b) := by
  rw [← cornerBalance_eq_totalTurnZ, ← cornerBalance_eq_totalTurnZ]
  exact singleton_cornerBalance_reduce v a b he




theorem jwd_unitCell_totalTurn (a : {e : Dart // IsBoundaryDart unitCell e})
    (ha : a.1 = ucDart0 ∨ a.1 = ucDart1 ∨ a.1 = ucDart2 ∨ a.1 = ucDart3) :
    totalTurnZ unitCell a.1 (dartOrbitPeriod unitCell a) = -4 := by
  rw [← cornerBalance_eq_totalTurnZ]
  exact unitCell_cornerBalance a ha










theorem jwd_singleton_turningIsFullRevolution (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}) :
    TurningIsFullRevolution ({v} : Set (Site 2)) a :=
  Or.inr (jwd_singleton_totalTurn v a)




theorem jwd_singleton_orbitPeriod_ge_four (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}) :
    4 ≤ dartOrbitPeriod ({v} : Set (Site 2)) a :=
  orbitPeriod_ge_four_of_fullRevolution ({v} : Set (Site 2)) a
    (jwd_singleton_turningIsFullRevolution v a)

end Walls

end StatMech
