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
import Code.Lattice.Cyclomatic

open SimpleGraph Function

namespace StatMech

namespace Lattice












noncomputable def gbCurvature (K : Set (Site 2)) (e : Dart) : ℤ := turnZ K e


theorem gbCurvature_mem (K : Set (Site 2)) (e : Dart) :
    gbCurvature K e = 1 ∨ gbCurvature K e = 0 ∨ gbCurvature K e = -1 :=
  turnZ_mem K e










theorem curvature_sum_eq_totalTurnZ (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    totalTurnZ K e p = ∑ i ∈ Finset.range p, gbCurvature K ((dartNext K)^[i] e) := rfl














noncomputable def revCount (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : ℤ :=
  totalTurnZ K a.1 (dartOrbitPeriod K a) / 4













theorem gaussBonnet_local_global (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 * revCount K a := by
  unfold revCount
  rw [Int.mul_ediv_cancel' (four_dvd_orbit_totalTurnZ K a)]












theorem turningIsFullRevolution_iff_revCount (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    TurningIsFullRevolution K a ↔ (revCount K a = 1 ∨ revCount K a = -1) := by
  unfold TurningIsFullRevolution
  rw [gaussBonnet_local_global K a]
  constructor
  · rintro (h | h)
    · left; omega
    · right; omega
  · rintro (h | h)
    · left; rw [h]; ring
    · right; rw [h]; ring



theorem turningIsFullRevolution_of_revCount (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (h : revCount K a = 1 ∨ revCount K a = -1) :
    TurningIsFullRevolution K a :=
  (turningIsFullRevolution_iff_revCount K a).mpr h
















theorem cycleGraph_card_edges (n : ℕ) :
    (cycleGraph (n + 3)).edgeFinset.card = n + 3 := by
  have hsum : ∑ v : Fin (n + 3), (cycleGraph (n + 3)).degree v
      = 2 * (cycleGraph (n + 3)).edgeFinset.card :=
    sum_degrees_eq_twice_card_edges _
  have hsum2 : ∑ v : Fin (n + 3), (cycleGraph (n + 3)).degree v = 2 * (n + 3) := by
    rw [Finset.sum_congr rfl (fun v _ => cycleGraph_degree_three_le)]
    simp [Finset.sum_const, Finset.card_univ]
    ring
  omega













theorem cycleGraph_cyclomaticNumber_eq_one (n : ℕ) :
    cyclomaticNumber (cycleGraph (n + 3)) = 1 := by
  unfold cyclomaticNumber
  rw [cycleGraph_card_edges]
  simp




theorem cycleGraph_not_isAcyclic (n : ℕ) : ¬ (cycleGraph (n + 3)).IsAcyclic := by
  rw [← cyclomaticNumber_eq_zero_iff_isAcyclic cycleGraph_connected]
  rw [cycleGraph_cyclomaticNumber_eq_one]
  decide















theorem orbitEnum_injective (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    Function.Injective
      (fun i : Fin (dartOrbitPeriod K a) => (dartNextSub K)^[i.val] a) := by
  intro i j h
  simp only at h
  have hmp : dartOrbitPeriod K a = Function.minimalPeriod (dartNextSub K) a := rfl
  have := Function.iterate_injOn_Iio_minimalPeriod (f := dartNextSub K) (x := a)
    (Set.mem_Iio.mpr (by rw [← hmp]; exact i.isLt))
    (Set.mem_Iio.mpr (by rw [← hmp]; exact j.isLt)) h
  exact Fin.ext this

open Classical in



theorem contour_card_darts (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (Finset.univ.image
      (fun i : Fin (dartOrbitPeriod K a) => (dartNextSub K)^[i.val] a)).card
      = dartOrbitPeriod K a := by
  rw [Finset.card_image_of_injective _ (orbitEnum_injective K a), Finset.card_univ,
    Fintype.card_fin]














noncomputable def contourEulerChar (p : ℕ) : ℕ := by
  classical
  exact if h : 3 ≤ p then cyclomaticNumber (cycleGraph p) else 0






theorem contourEulerChar_eq_one {p : ℕ} (hp : 3 ≤ p) : contourEulerChar p = 1 := by
  unfold contourEulerChar
  rw [dif_pos hp]
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 3 := ⟨p - 3, by omega⟩
  exact cycleGraph_cyclomaticNumber_eq_one n































def EulerCharOne (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  revCount K a = (contourEulerChar (dartOrbitPeriod K a) : ℤ) ∨
    revCount K a = -(contourEulerChar (dartOrbitPeriod K a) : ℤ)










theorem turningIsFullRevolution_of_eulerCharOne (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (h : EulerCharOne K a) :
    TurningIsFullRevolution K a := by
  apply turningIsFullRevolution_of_revCount
  have hchi : contourEulerChar (dartOrbitPeriod K a) = 1 := contourEulerChar_eq_one hp
  rcases h with h | h
  · left; rw [h, hchi]; rfl
  · right; rw [h, hchi]; rfl











theorem eulerCharOne_iff_turningIsFullRevolution (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a) :
    EulerCharOne K a ↔ TurningIsFullRevolution K a := by
  constructor
  · exact turningIsFullRevolution_of_eulerCharOne K a hp
  · intro h
    have hchi : contourEulerChar (dartOrbitPeriod K a) = 1 := contourEulerChar_eq_one hp
    unfold EulerCharOne
    rw [hchi]
    rcases (turningIsFullRevolution_iff_revCount K a).mp h with h1 | h1
    · left; rw [h1]; rfl
    · right; rw [h1]; rfl












theorem unitCell_eulerCharOne : EulerCharOne unitCell ucBase := by
  have hp : 3 ≤ dartOrbitPeriod unitCell ucBase := by
    rw [unitCell_orbitPeriod_eq_four]; norm_num
  exact (eulerCharOne_iff_turningIsFullRevolution unitCell ucBase hp).mpr
    unitCell_turningIsFullRevolution





theorem domino_eulerCharOne : EulerCharOne domino dmBase := by
  have hp : 3 ≤ dartOrbitPeriod domino dmBase := by
    rw [domino_orbitPeriod_eq_six]; norm_num
  exact (eulerCharOne_iff_turningIsFullRevolution domino dmBase hp).mpr
    domino_turningIsFullRevolution

end Lattice

end StatMech
