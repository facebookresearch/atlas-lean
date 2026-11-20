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
import Code.Lattice.EarRemoval
import Code.Lattice.EarContraction
import Code.Lattice.GaussBonnet

open SimpleGraph Function

namespace StatMech.Walls

open StatMech.Lattice
























theorem cornerBalance_eq_four_revCount (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    cornerBalance K a = 4 * revCount K a := by
  rw [cornerBalance_eq_totalTurnZ, gaussBonnet_local_global]











theorem cornerBalance_eq_four_iff_revCount_eq_one (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (cornerBalance K a = 4 ∨ cornerBalance K a = -4) ↔
      (revCount K a = 1 ∨ revCount K a = -1) := by
  rw [cornerBalance_eq_four_revCount]
  omega













theorem eulerCharOne_iff_revCount_eq_one (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a) :
    EulerCharOne K a ↔ (revCount K a = 1 ∨ revCount K a = -1) := by
  unfold EulerCharOne
  rw [contourEulerChar_eq_one hp]
  norm_num





















theorem routes_coincide (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) :
    ((cornerBalance K a = 4 ∨ cornerBalance K a = -4) ↔
        (revCount K a = 1 ∨ revCount K a = -1)) ∧
      (EulerCharOne K a ↔ (revCount K a = 1 ∨ revCount K a = -1)) ∧
      (TurningIsFullRevolution K a ↔ (revCount K a = 1 ∨ revCount K a = -1)) := by
  refine ⟨cornerBalance_eq_four_iff_revCount_eq_one K a,
    eulerCharOne_iff_revCount_eq_one K a hp, ?_⟩
  exact turningIsFullRevolution_iff_revCount K a





theorem cornerBalance_eq_four_iff_turningIsFullRevolution (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (cornerBalance K a = 4 ∨ cornerBalance K a = -4) ↔ TurningIsFullRevolution K a := by
  rw [cornerBalance_eq_four_iff_revCount_eq_one, ← turningIsFullRevolution_iff_revCount]





theorem eulerCharOne_iff_cornerBalance_eq_four (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a) :
    EulerCharOne K a ↔ (cornerBalance K a = 4 ∨ cornerBalance K a = -4) := by
  rw [eulerCharOne_iff_revCount_eq_one K a hp, ← cornerBalance_eq_four_iff_revCount_eq_one]











theorem unitCell_revCount_eq_neg_one : revCount unitCell ucBase = -1 := by
  have h : cornerBalance unitCell ucBase = -4 := unitCell_cornerBalance ucBase (Or.inl rfl)
  rw [cornerBalance_eq_four_revCount] at h
  omega



theorem domino_cornerBalance_eq_neg_four : cornerBalance domino dmBase = -4 := by
  rw [cornerBalance_eq_totalTurnZ, show (dmBase).1 = dmD0 from rfl,
    domino_orbitPeriod_eq_six]
  exact domino_totalTurnZ_six




theorem domino_revCount_eq_neg_one : revCount domino dmBase = -1 := by
  have h := domino_cornerBalance_eq_neg_four
  rw [cornerBalance_eq_four_revCount] at h
  omega




theorem unitCell_routes_coincide :
    ((cornerBalance unitCell ucBase = 4 ∨ cornerBalance unitCell ucBase = -4) ↔
        (revCount unitCell ucBase = 1 ∨ revCount unitCell ucBase = -1)) ∧
      (EulerCharOne unitCell ucBase ↔
        (revCount unitCell ucBase = 1 ∨ revCount unitCell ucBase = -1)) ∧
      (TurningIsFullRevolution unitCell ucBase ↔
        (revCount unitCell ucBase = 1 ∨ revCount unitCell ucBase = -1)) :=
  routes_coincide unitCell ucBase (by rw [unitCell_orbitPeriod_eq_four]; norm_num)



theorem domino_routes_coincide :
    ((cornerBalance domino dmBase = 4 ∨ cornerBalance domino dmBase = -4) ↔
        (revCount domino dmBase = 1 ∨ revCount domino dmBase = -1)) ∧
      (EulerCharOne domino dmBase ↔
        (revCount domino dmBase = 1 ∨ revCount domino dmBase = -1)) ∧
      (TurningIsFullRevolution domino dmBase ↔
        (revCount domino dmBase = 1 ∨ revCount domino dmBase = -1)) :=
  routes_coincide domino dmBase (by rw [domino_orbitPeriod_eq_six]; norm_num)

end StatMech.Walls
