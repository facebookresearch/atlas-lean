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
import Code.Lattice.GaussBonnet
import Code.Lattice.JordanOrbitCycle

open scoped BigOperators
open SimpleGraph Function

namespace StatMech

namespace Lattice










def umf_WindsAtMostOnce (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ 4




def umf_WindsAtLeastOnce (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  totalTurnZ K a.1 (dartOrbitPeriod K a) ≠ 0







theorem umf_totalTurn_eq_four_of_winds (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hmax : umf_WindsAtMostOnce K a) (hmin : umf_WindsAtLeastOnce K a) :
    totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
      totalTurnZ K a.1 (dartOrbitPeriod K a) = -4 := by
  have hdvd := four_dvd_orbit_totalTurnZ K a
  unfold umf_WindsAtMostOnce at hmax
  unfold umf_WindsAtLeastOnce at hmin
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at hmax hmin ⊢
  rw [abs_le] at hmax
  have hk1 : k = 1 ∨ k = -1 := by
    rcases lt_trichotomy k 0 with h | h | h
    · right; omega
    · exact absurd (by rw [h]; ring) hmin
    · left; omega
  rcases hk1 with h | h
  · left; rw [h]; ring
  · right; rw [h]; ring


theorem umf_turningIsFullRevolution_of_winds (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hmax : umf_WindsAtMostOnce K a) (hmin : umf_WindsAtLeastOnce K a) :
    TurningIsFullRevolution K a :=
  umf_totalTurn_eq_four_of_winds K a hmax hmin


theorem umf_winds_of_fullRevolution (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : TurningIsFullRevolution K a) :
    umf_WindsAtMostOnce K a ∧ umf_WindsAtLeastOnce K a := by
  unfold umf_WindsAtMostOnce umf_WindsAtLeastOnce
  rcases h with h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩





theorem umf_winds_iff (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (umf_WindsAtMostOnce K a ∧ umf_WindsAtLeastOnce K a) ↔ TurningIsFullRevolution K a := by
  constructor
  · rintro ⟨hmax, hmin⟩; exact umf_turningIsFullRevolution_of_winds K a hmax hmin
  · exact umf_winds_of_fullRevolution K a










theorem umf_eulerCharOne_iff_winds (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a) :
    EulerCharOne K a ↔ (umf_WindsAtMostOnce K a ∧ umf_WindsAtLeastOnce K a) := by
  rw [eulerCharOne_iff_turningIsFullRevolution K a hp, ← umf_winds_iff]




theorem umf_eulerCharOne_iff_turningIsFullRevolution (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a) :
    EulerCharOne K a ↔ TurningIsFullRevolution K a :=
  eulerCharOne_iff_turningIsFullRevolution K a hp




theorem umf_fullRevolution_of_eulerCharOne (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (h : EulerCharOne K a) :
    TurningIsFullRevolution K a :=
  turningIsFullRevolution_of_eulerCharOne K a hp h






theorem umf_revCount_of_eulerCharOne (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (h : EulerCharOne K a) :
    revCount K a = 1 ∨ revCount K a = -1 :=
  (turningIsFullRevolution_iff_revCount K a).mp (umf_fullRevolution_of_eulerCharOne K a hp h)



theorem umf_eulerCharOne_of_revCount_pm_one (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (h : revCount K a = 1 ∨ revCount K a = -1) :
    EulerCharOne K a :=
  (umf_eulerCharOne_iff_turningIsFullRevolution K a hp).mpr
    (turningIsFullRevolution_of_revCount K a h)











theorem umf_convex_minus_reflex_eq (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    leftCornerCount K e p - rightCornerCount K e p = - totalTurnZ K e p := by
  rw [totalTurnZ_eq_cornerBalance]; ring

theorem umf_leftCornerCount_nonneg (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    0 ≤ leftCornerCount K e p := by
  unfold leftCornerCount; exact_mod_cast Nat.zero_le _

theorem umf_rightCornerCount_nonneg (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    0 ≤ rightCornerCount K e p := by
  unfold rightCornerCount; exact_mod_cast Nat.zero_le _





theorem umf_four_convex_of_totalTurn_neg (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (h : totalTurnZ K a.1 (dartOrbitPeriod K a) = -4) :
    4 ≤ leftCornerCount K a.1 (dartOrbitPeriod K a) := by
  have hbal := umf_convex_minus_reflex_eq K a.1 (dartOrbitPeriod K a)
  rw [h] at hbal
  have hr := umf_rightCornerCount_nonneg K a.1 (dartOrbitPeriod K a)
  linarith


theorem umf_four_reflex_of_totalTurn_pos (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (h : totalTurnZ K a.1 (dartOrbitPeriod K a) = 4) :
    4 ≤ rightCornerCount K a.1 (dartOrbitPeriod K a) := by
  have hbal := umf_convex_minus_reflex_eq K a.1 (dartOrbitPeriod K a)
  rw [h] at hbal
  have hl := umf_leftCornerCount_nonneg K a.1 (dartOrbitPeriod K a)
  linarith



theorem umf_four_corners_of_fullRevolution (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : TurningIsFullRevolution K a) :
    4 ≤ leftCornerCount K a.1 (dartOrbitPeriod K a) ∨
      4 ≤ rightCornerCount K a.1 (dartOrbitPeriod K a) := by
  rcases h with h | h
  · exact Or.inr (umf_four_reflex_of_totalTurn_pos K a h)
  · exact Or.inl (umf_four_convex_of_totalTurn_neg K a h)






theorem umf_four_convex_or_reflex_of_eulerCharOne (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (h : EulerCharOne K a) :
    4 ≤ leftCornerCount K a.1 (dartOrbitPeriod K a) ∨
      4 ≤ rightCornerCount K a.1 (dartOrbitPeriod K a) :=
  umf_four_corners_of_fullRevolution K a (umf_fullRevolution_of_eulerCharOne K a hp h)




theorem umf_four_convex_of_eulerCharOne_neg (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (_hp : 3 ≤ dartOrbitPeriod K a) (_h : EulerCharOne K a)
    (hor : totalTurnZ K a.1 (dartOrbitPeriod K a) = -4) :
    4 ≤ leftCornerCount K a.1 (dartOrbitPeriod K a) :=
  umf_four_convex_of_totalTurn_neg K a hor









theorem umf_unitCell_fullRevolution : TurningIsFullRevolution unitCell ucBase :=
  unitCell_turningIsFullRevolution



theorem umf_unitCell_totalTurn_neg :
    totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 := by
  rw [show (ucBase).1 = ucDart0 from rfl, unitCell_orbitPeriod_eq_four]
  exact unitCell_totalTurnZ_four


theorem umf_unitCell_eulerCharOne : EulerCharOne unitCell ucBase := unitCell_eulerCharOne


theorem umf_unitCell_revCount : revCount unitCell ucBase = -1 := by
  have hp : (3 : ℕ) ≤ dartOrbitPeriod unitCell ucBase := by
    rw [unitCell_orbitPeriod_eq_four]; norm_num
  have h := umf_revCount_of_eulerCharOne unitCell ucBase hp umf_unitCell_eulerCharOne
  rcases h with h | h
  · exfalso
    have := gaussBonnet_local_global unitCell ucBase
    rw [h, umf_unitCell_totalTurn_neg] at this; norm_num at this
  · exact h




theorem umf_unitCell_four_convex :
    4 ≤ leftCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) :=
  umf_four_convex_of_totalTurn_neg unitCell ucBase umf_unitCell_totalTurn_neg



theorem umf_unitCell_convex_minus_reflex :
    leftCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase)
      - rightCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 4 := by
  rw [umf_convex_minus_reflex_eq, umf_unitCell_totalTurn_neg]; norm_num












def umf_Ltromino : Set (Site 2) := joc_Ltromino



theorem umf_Ltromino_kingSaturated : npm_KingSaturated umf_Ltromino :=
  joc_Ltromino_kingSaturated





theorem umf_Ltromino_faceMultiplicityOne (a : {e : Dart // IsBoundaryDart umf_Ltromino e}) :
    usc_FaceMultiplicityOne umf_Ltromino a :=
  joc_Ltromino_faceMultiplicityOne a

































end Lattice

end StatMech
