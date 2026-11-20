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
import Code.Lattice.StarHullUmlaufsatz

open scoped BigOperators
open SimpleGraph Function

namespace StatMech

namespace Lattice








theorem uml_four_dvd_totalTurn (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (4 : ℤ) ∣ totalTurnZ K a.1 (dartOrbitPeriod K a) :=
  four_dvd_orbit_totalTurnZ K a












theorem uml_cornerBalance_eq_totalTurn (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    leftCornerCount K e p - rightCornerCount K e p = - totalTurnZ K e p := by
  rw [totalTurnZ_eq_cornerBalance]; ring


theorem uml_leftCornerCount_nonneg (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    0 ≤ leftCornerCount K e p := by
  unfold leftCornerCount; exact_mod_cast Nat.zero_le _


theorem uml_rightCornerCount_nonneg (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    0 ≤ rightCornerCount K e p := by
  unfold rightCornerCount; exact_mod_cast Nat.zero_le _













theorem uml_four_convex_minus_reflex (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : TurningIsFullRevolution K a) :
    leftCornerCount K a.1 (dartOrbitPeriod K a)
        - rightCornerCount K a.1 (dartOrbitPeriod K a) = 4 ∨
      leftCornerCount K a.1 (dartOrbitPeriod K a)
        - rightCornerCount K a.1 (dartOrbitPeriod K a) = -4 := by
  have hbal := uml_cornerBalance_eq_totalTurn K a.1 (dartOrbitPeriod K a)
  rcases h with h | h
  · right; rw [hbal, h]
  · left; rw [hbal, h]; norm_num






theorem uml_four_convex_of_totalTurn_neg_four (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (h : totalTurnZ K a.1 (dartOrbitPeriod K a) = -4) :
    4 ≤ leftCornerCount K a.1 (dartOrbitPeriod K a) := by
  have hbal := uml_cornerBalance_eq_totalTurn K a.1 (dartOrbitPeriod K a)
  rw [h] at hbal
  have hr := uml_rightCornerCount_nonneg K a.1 (dartOrbitPeriod K a)
  linarith



theorem uml_four_reflex_of_totalTurn_four (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (h : totalTurnZ K a.1 (dartOrbitPeriod K a) = 4) :
    4 ≤ rightCornerCount K a.1 (dartOrbitPeriod K a) := by
  have hbal := uml_cornerBalance_eq_totalTurn K a.1 (dartOrbitPeriod K a)
  rw [h] at hbal
  have hl := uml_leftCornerCount_nonneg K a.1 (dartOrbitPeriod K a)
  linarith






theorem uml_four_convex_of_fullRevolution (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : TurningIsFullRevolution K a) :
    4 ≤ leftCornerCount K a.1 (dartOrbitPeriod K a) ∨
      4 ≤ rightCornerCount K a.1 (dartOrbitPeriod K a) := by
  rcases h with h | h
  · exact Or.inr (uml_four_reflex_of_totalTurn_four K a h)
  · exact Or.inl (uml_four_convex_of_totalTurn_neg_four K a h)



theorem uml_one_le_convex_of_fullRevolution (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : TurningIsFullRevolution K a) :
    1 ≤ leftCornerCount K a.1 (dartOrbitPeriod K a) ∨
      1 ≤ rightCornerCount K a.1 (dartOrbitPeriod K a) := by
  rcases uml_four_convex_of_fullRevolution K a h with h4 | h4
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)













theorem uml_unitCell_totalTurn_neg_four :
    totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 := by
  rw [show (ucBase).1 = ucDart0 from rfl, unitCell_orbitPeriod_eq_four]
  exact unitCell_totalTurnZ_four





theorem uml_unitCell_four_convex :
    4 ≤ leftCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) :=
  uml_four_convex_of_totalTurn_neg_four unitCell ucBase uml_unitCell_totalTurn_neg_four




theorem uml_unitCell_convex_minus_reflex :
    leftCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase)
      - rightCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 4 := by
  have hbal := uml_cornerBalance_eq_totalTurn unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase)
  rw [hbal, uml_unitCell_totalTurn_neg_four]; norm_num
















theorem uml_starHull_four_corners_of_balanceIsFour (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (h : BalanceIsFour (ndt_StarHull K) a) :
    4 ≤ leftCornerCount (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) ∨
      4 ≤ rightCornerCount (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) := by
  apply uml_four_convex_of_fullRevolution
  unfold TurningIsFullRevolution
  exact shu_totalTurn_eq_four_of_balanceIsFour K a h






theorem uml_starHull_four_convex_of_totalTurn_neg_four (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (h : totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4) :
    4 ≤ leftCornerCount (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) :=
  uml_four_convex_of_totalTurn_neg_four (ndt_StarHull K) a h

end Lattice

end StatMech
