/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.Lattice.GaussBonnet
import Code.Lattice.TurningNumber
import Code.Walls.euceuler

open SimpleGraph Function

namespace StatMech

namespace Lattice











theorem wgb_revCount_iff_eulerCharOne (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a) :
    EulerCharOne K a ↔ (revCount K a = 1 ∨ revCount K a = -1) := by
  rw [eulerCharOne_iff_turningIsFullRevolution K a hp, turningIsFullRevolution_iff_revCount]









def wgb_WindsAtMostOnce (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  |revCount K a| ≤ 1


def wgb_WindsAtLeastOnce (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  revCount K a ≠ 0




theorem wgb_revCount_pm_one_iff_windsBoth (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (revCount K a = 1 ∨ revCount K a = -1) ↔
      (wgb_WindsAtMostOnce K a ∧ wgb_WindsAtLeastOnce K a) := by
  unfold wgb_WindsAtMostOnce wgb_WindsAtLeastOnce
  constructor
  · rintro (h | h) <;> rw [h] <;> exact ⟨by decide, by decide⟩
  · rintro ⟨hmax, hmin⟩
    rw [abs_le] at hmax
    omega



theorem wgb_windsAtMostOnce_iff (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    wgb_WindsAtMostOnce K a ↔
      |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ 4 := by
  unfold wgb_WindsAtMostOnce
  rw [gaussBonnet_local_global K a, abs_mul]
  simp only [show |(4 : ℤ)| = 4 from rfl]
  constructor
  · intro h; nlinarith [abs_nonneg (revCount K a)]
  · intro h; nlinarith [abs_nonneg (revCount K a)]



theorem wgb_windsAtLeastOnce_iff (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    wgb_WindsAtLeastOnce K a ↔
      totalTurnZ K a.1 (dartOrbitPeriod K a) ≠ 0 := by
  unfold wgb_WindsAtLeastOnce
  rw [gaussBonnet_local_global K a]
  omega











theorem wgb_revCount_abs_le_period (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    |revCount K a| ≤ (dartOrbitPeriod K a : ℤ) := by
  have hb : |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ (dartOrbitPeriod K a : ℤ) :=
    abs_totalTurnZ_le K a.1 (dartOrbitPeriod K a)
  rw [gaussBonnet_local_global K a, abs_mul] at hb
  simp only [show |(4 : ℤ)| = 4 from rfl] at hb
  nlinarith [abs_nonneg (revCount K a)]







theorem wgb_turningBound_weaker_than_windsAtMostOnce :
    ∃ (p : ℕ) (r : ℤ), 4 ≤ p ∧ |r| ≤ (p : ℤ) ∧ ¬ (|r| ≤ 1) := by
  exact ⟨8, 2, by norm_num, by norm_num, by norm_num⟩











theorem wgb_contourEulerChar_carries_no_winding {p : ℕ} (hp : 3 ≤ p) :
    contourEulerChar p = 1 :=
  contourEulerChar_eq_one hp





theorem wgb_eulerCharOne_is_revCount_pm_one (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a) :
    EulerCharOne K a ↔ (revCount K a = 1 ∨ revCount K a = -1) :=
  wgb_revCount_iff_eulerCharOne K a hp










theorem wgb_regChi_holeyRing_ne_one :
    StatMech.Euc.regChi
      ({((0:ℤ),(0:ℤ)),(1,0),(2,0),(0,1),(2,1),(0,2),(1,2),(2,2)} : Finset StatMech.Euc.Cell)
      ≠ 1 := by
  rw [StatMech.Euc.euc_chi_holeyRing]; decide



theorem wgb_regChi_eq_one_of_buildable {K : Finset StatMech.Euc.Cell}
    (hK : StatMech.Euc.EucBuildable K) : StatMech.Euc.regChi K = 1 :=
  StatMech.Euc.euc_chi_induction hK








theorem wgb_revCount_pm_one_of_eulerCharOne (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a)
    (h : EulerCharOne K a) :
    revCount K a = 1 ∨ revCount K a = -1 :=
  (wgb_revCount_iff_eulerCharOne K a hp).mp h









theorem wgb_unitCell_revCount_pm_one :
    revCount unitCell ucBase = 1 ∨ revCount unitCell ucBase = -1 :=
  (turningIsFullRevolution_iff_revCount unitCell ucBase).mp unitCell_turningIsFullRevolution



theorem wgb_domino_revCount_pm_one :
    revCount domino dmBase = 1 ∨ revCount domino dmBase = -1 :=
  (turningIsFullRevolution_iff_revCount domino dmBase).mp domino_turningIsFullRevolution

end Lattice

end StatMech
