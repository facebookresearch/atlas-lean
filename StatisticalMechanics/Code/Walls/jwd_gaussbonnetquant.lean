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
import Code.Lattice.GaussBonnet
import Code.Lattice.CornerBalance
import Code.Lattice.CrossingParity
import Code.Lattice.InteriorWindingClose
import Code.Lattice.OrbitSeparatesProof
import Code.Lattice.LexMinOrientation

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice




















theorem jwd_totalTurn_quantised_of_closed (K : Set (Site 2)) (e : Dart) (p : ℕ)
    (hp : (dartNext K)^[p] e = e) :
    ∃ k : ℤ, totalTurnZ K e p = 4 * k :=
  four_dvd_totalTurnZ_of_iterate_eq K e p hp





















theorem jwd_gaussBonnet_quantisation (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 * revCount K a :=
  gaussBonnet_local_global K a





theorem jwd_revCount_spec (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 * revCount K a ∧
      ∀ k : ℤ, totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 * k → k = revCount K a := by
  refine ⟨gaussBonnet_local_global K a, fun k hk => ?_⟩
  have h := gaussBonnet_local_global K a
  
  have : (4 : ℤ) * k = 4 * revCount K a := by rw [← hk, h]
  exact mul_left_cancel₀ (by norm_num) this











theorem jwd_curvature_sum_eq_four_revCount (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (∑ i ∈ Finset.range (dartOrbitPeriod K a),
        gbCurvature K ((dartNext K)^[i] a.1)) = 4 * revCount K a := by
  rw [← curvature_sum_eq_totalTurnZ K a.1 (dartOrbitPeriod K a)]
  exact gaussBonnet_local_global K a




theorem jwd_totalTurn_eq_four_mul (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    ∃ k : ℤ, totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 * k :=
  ⟨revCount K a, gaussBonnet_local_global K a⟩












theorem jwd_unitCell_totalTurn_gbq :
    totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 := by
  rw [show (ucBase).1 = ucDart0 from rfl, unitCell_orbitPeriod_eq_four]
  exact unitCell_totalTurnZ_four






theorem jwd_unitCell_quantisation :
    totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase)
        = 4 * revCount unitCell ucBase ∧
      revCount unitCell ucBase = -1 := by
  refine ⟨gaussBonnet_local_global unitCell ucBase, ?_⟩
  
  have hgb := gaussBonnet_local_global unitCell ucBase
  rw [jwd_unitCell_totalTurn_gbq] at hgb
  
  omega




theorem jwd_domino_totalTurn :
    totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = -4 := by
  rw [show (dmBase).1 = dmD0 from rfl, domino_orbitPeriod_eq_six]
  exact domino_totalTurnZ_six





theorem jwd_domino_quantisation :
    totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase)
        = 4 * revCount domino dmBase ∧
      revCount domino dmBase = -1 := by
  refine ⟨gaussBonnet_local_global domino dmBase, ?_⟩
  have hgb := gaussBonnet_local_global domino dmBase
  rw [jwd_domino_totalTurn] at hgb
  omega

end Walls

end StatMech
