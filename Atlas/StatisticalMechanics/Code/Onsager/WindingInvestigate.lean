/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.Lattice.TurningNumber
import Code.Lattice.EarContraction
import Code.Lattice.EarRemoval
import Code.Lattice.GaussBonnet
import Code.Lattice.GaussBonnetEar
import Code.Lattice.BalanceContraction
import Code.Lattice.BalancePreservingContraction
import Code.Lattice.TotalTurnFour

open SimpleGraph Function Set

namespace StatMech

namespace Lattice












theorem wi_totalTurn_eq_four_of_winds (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hmax : |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ 4)
    (hmin : totalTurnZ K a.1 (dartOrbitPeriod K a) ≠ 0) :
    totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
      totalTurnZ K a.1 (dartOrbitPeriod K a) = -4 := by
  obtain ⟨k, hk⟩ := four_dvd_orbit_totalTurnZ K a
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






theorem wi_winds_iff (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (|totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ 4 ∧
      totalTurnZ K a.1 (dartOrbitPeriod K a) ≠ 0) ↔
      TurningIsFullRevolution K a := by
  unfold TurningIsFullRevolution
  constructor
  · rintro ⟨hmax, hmin⟩; exact wi_totalTurn_eq_four_of_winds K a hmax hmin
  · rintro (h | h) <;> rw [h] <;> exact ⟨by decide, by decide⟩
















theorem wi_turningIsFullRevolution_of_saturating
    (hsat : bpc_BalanceSaturatingContraction)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) :
    TurningIsFullRevolution K a :=
  turningIsFullRevolution_of_contraction
    (bpc_balancePreservingContraction_of_saturating hsat) K hK hne a



theorem wi_totalTurn_eq_four_of_saturating
    (hsat : bpc_BalanceSaturatingContraction)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
      totalTurnZ K a.1 (dartOrbitPeriod K a) = -4 :=
  wi_turningIsFullRevolution_of_saturating hsat K hK hne a





theorem wi_winds_of_saturating
    (hsat : bpc_BalanceSaturatingContraction)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) :
    |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ 4 ∧
      totalTurnZ K a.1 (dartOrbitPeriod K a) ≠ 0 :=
  (wi_winds_iff K a).mpr (wi_turningIsFullRevolution_of_saturating hsat K hK hne a)





theorem wi_eulerCharOne_of_saturating
    (hsat : bpc_BalanceSaturatingContraction)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a) :
    EulerCharOne K a :=
  (eulerCharOne_iff_turningIsFullRevolution K a hp).mpr
    (wi_turningIsFullRevolution_of_saturating hsat K hK hne a)










theorem wi_ttf_winds_of_saturating
    (hsat : bpc_BalanceSaturatingContraction)
    (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    ttf_WindsAtMostOnce K a ∧ ttf_WindsAtLeastOnce K a :=
  ttf_winds_of_totalTurn_eq_four K a
    (bpc_totalTurn_eq_four_value_of_saturating K hSK hne a hsat)









theorem wi_residue_chain (hsat : bpc_BalanceSaturatingContraction) :
    BalancePreservingContraction :=
  bpc_balancePreservingContraction_of_saturating hsat





theorem wi_domino_saturating_witness :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < domino.ncard ∧ cornerBalance K' a' = cornerBalance domino dmBase :=
  bpc_domino_balanceSaturatingContraction_witness






















































end Lattice

end StatMech
