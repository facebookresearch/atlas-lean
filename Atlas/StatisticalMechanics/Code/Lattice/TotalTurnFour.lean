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
import Code.Lattice.Umlaufsatz
import Code.Lattice.UmlaufsatzSingleCycle
import Code.Lattice.NoPinchDual
import Code.Lattice.NoPinchMatching
import Code.Lattice.Wall1EmbeddingRetry
import Code.Lattice.NoDiagTouchClose
import Code.Lattice.WindingWitness

open SimpleGraph Function Set Finset

namespace StatMech

namespace Lattice











theorem ttf_four_dvd_totalTurn (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    (4 : ℤ) ∣ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) :=
  four_dvd_orbit_totalTurnZ (ndt_StarHull K) a




theorem ttf_abs_totalTurn_le_period (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    |totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a)|
      ≤ (dartOrbitPeriod (ndt_StarHull K) a : ℤ) :=
  abs_orbit_totalTurnZ_le (ndt_StarHull K) a










theorem ttf_localTurn_mem (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) (f : Site 2) :
    usc_localTurn (ndt_StarHull K) a f = 1 ∨ usc_localTurn (ndt_StarHull K) a f = 0 ∨
      usc_localTurn (ndt_StarHull K) a f = -1 :=
  wwit_starHull_localTurn_mem K a f




theorem ttf_totalTurn_eq_sum_localTurn (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a)
      = ∑ f ∈ usc_orbitFaces (ndt_StarHull K) a, usc_localTurn (ndt_StarHull K) a f :=
  usc_totalTurnZ_eq_sum_localTurn (ndt_StarHull K) a













def ttf_WindsAtMostOnce (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) : Prop :=
  |totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a)| ≤ 4





def ttf_WindsAtLeastOnce (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) : Prop :=
  totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) ≠ 0






theorem ttf_totalTurn_eq_four_of_winds (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hmax : ttf_WindsAtMostOnce K a) (hmin : ttf_WindsAtLeastOnce K a) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 := by
  have hdvd := ttf_four_dvd_totalTurn K a
  unfold ttf_WindsAtMostOnce at hmax
  unfold ttf_WindsAtLeastOnce at hmin
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




theorem ttf_turningIsFullRevolution_of_winds (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hmax : ttf_WindsAtMostOnce K a) (hmin : ttf_WindsAtLeastOnce K a) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  ttf_totalTurn_eq_four_of_winds K a hmax hmin









theorem ttf_winds_of_totalTurn_eq_four (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (h : totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4) :
    ttf_WindsAtMostOnce K a ∧ ttf_WindsAtLeastOnce K a := by
  unfold ttf_WindsAtMostOnce ttf_WindsAtLeastOnce
  rcases h with h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩






theorem ttf_winds_iff (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    (ttf_WindsAtMostOnce K a ∧ ttf_WindsAtLeastOnce K a) ↔
      (totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
        totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4) := by
  constructor
  · rintro ⟨hmax, hmin⟩; exact ttf_totalTurn_eq_four_of_winds K a hmax hmin
  · exact ttf_winds_of_totalTurn_eq_four K a











theorem ttf_totalTurn_eq_four_of_eulerCharOne (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a)
    (h : EulerCharOne (ndt_StarHull K) a) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  turningIsFullRevolution_of_eulerCharOne (ndt_StarHull K) a hp h





theorem ttf_eulerCharOne_iff_winds (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a) :
    EulerCharOne (ndt_StarHull K) a ↔
      (ttf_WindsAtMostOnce K a ∧ ttf_WindsAtLeastOnce K a) := by
  rw [eulerCharOne_iff_turningIsFullRevolution (ndt_StarHull K) a hp]
  unfold TurningIsFullRevolution
  rw [ttf_winds_iff]












theorem ttf_totalTurn_eq_four_of_balancePreservingContraction (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hcontr : BalancePreservingContraction) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  turningIsFullRevolution_of_contraction hcontr (ndt_StarHull K) hSK hne a













theorem ttf_unitCell_totalTurn_eq_four :
    totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 4 ∨
      totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 :=
  unitCell_turningIsFullRevolution



theorem ttf_unitCell_winds :
    |totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase)| ≤ 4 ∧
      totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) ≠ 0 := by
  rcases ttf_unitCell_totalTurn_eq_four with h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩





theorem ttf_domino_totalTurn_eq_four :
    totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = 4 ∨
      totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = -4 :=
  domino_turningIsFullRevolution





































end Lattice

end StatMech
