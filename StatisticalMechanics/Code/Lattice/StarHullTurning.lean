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
import Code.Lattice.EarExistence
import Code.Lattice.EarContraction
import Code.Lattice.GaussBonnet
import Code.Lattice.GaussBonnetEar
import Code.Lattice.BalanceContraction
import Code.Lattice.BalancePreservingContraction
import Code.Lattice.TotalTurnFour
import Code.Lattice.NoPinchDual
import Code.Lattice.NoPinchMatching
import Code.Lattice.Wall1EmbeddingRetry
import Code.Lattice.NoDiagTouchClose
import Code.Lattice.StarHullFinite
import Code.Lattice.StarHullPeriod

open Set SimpleGraph Function

namespace StatMech

namespace Lattice









theorem sht_starHull_finite (K : Set (Site 2)) (hK : K.Finite) : (ndt_StarHull K).Finite :=
  starHull_finite K hK


theorem sht_starHull_nonempty (K : Set (Site 2)) (hne : K.Nonempty) : (ndt_StarHull K).Nonempty :=
  hne.mono (ndt_subset_starHull K)



theorem sht_starHull_period_ge_three (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    3 ≤ dartOrbitPeriod (ndt_StarHull K) a :=
  shp_starHull_period_ge_three K hK a



theorem sht_starHull_orbit_isCycle (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    ((dartOrbitFaceWalk (ndt_StarHull K) a.1 a.2 (dartOrbitPeriod (ndt_StarHull K) a)).copy rfl
      (by rw [orbit_iterate_period_eq (ndt_StarHull K) a])).IsCycle :=
  ndt_orbit_isCycle K a (sht_starHull_period_ge_three K hK a)










theorem sht_vec2_eq (a b c d : ℤ) : (![a, b] : Site 2) = ![c, d] ↔ a = c ∧ b = d := by
  rw [funext_iff, Fin.forall_fin_two]; simp







theorem sht_cutWitness_kingSaturated : npm_KingSaturated cutWitness := by
  intro f
  have hP00 : npd_P00 f = ![f 0, f 1] := rfl
  have hP10 : npd_P10 f = ![f 0 + 1, f 1] := rfl
  have hP11 : npd_P11 f = ![f 0 + 1, f 1 + 1] := rfl
  have hP01 : npd_P01 f = ![f 0, f 1 + 1] := rfl
  simp only [mem_cutWitness, hP00, hP10, hP11, hP01, sht_vec2_eq]
  omega


theorem sht_cutWitness_finite : cutWitness.Finite := by
  unfold cutWitness; exact Set.toFinite _


theorem sht_cutWitness_nonempty : cutWitness.Nonempty := ⟨_, cw_v00⟩







theorem sht_cutWitness_orbit_isCycle (a : {e : Dart // IsBoundaryDart cutWitness e}) :
    ((dartOrbitFaceWalk cutWitness a.1 a.2 (dartOrbitPeriod cutWitness a)).copy rfl
      (by rw [orbit_iterate_period_eq cutWitness a])).IsCycle :=
  emb_orbit_isCycle_of_kingSaturated cutWitness a
    (shp_period_ge_three cutWitness sht_cutWitness_finite a) sht_cutWitness_kingSaturated





theorem sht_cutWitness_extreme_convex : turnZ cutWitness (leftDart ![1, 1]) = -1 :=
  extremeCell_turnZ cutWitness ![1, 1] cutWitness_extreme






theorem sht_cutWitness_convex_corner_disconnects :
    ¬ CellConnected (cutWitness \ {![1, 1]}) :=
  cutWitness_diff_not_cellConnected













theorem sht_kingSat_singleCycle_convex_corner_can_disconnect :
    ∃ (K : Set (Site 2)) (c : Site 2),
      K.Finite ∧ K.Nonempty ∧ npm_KingSaturated K ∧ IsExtremeCell K c ∧
      turnZ K (leftDart c) = -1 ∧ ¬ CellConnected (K \ {c}) :=
  ⟨cutWitness, ![1, 1], sht_cutWitness_finite, sht_cutWitness_nonempty,
    sht_cutWitness_kingSaturated, cutWitness_extreme, sht_cutWitness_extreme_convex,
    sht_cutWitness_convex_corner_disconnects⟩


















theorem sht_totalTurn_eq_four_of_saturating (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hsat : bpc_BalanceSaturatingContraction) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 :=
  bpc_totalTurn_eq_four_value_of_saturating K (sht_starHull_finite K hK)
    (sht_starHull_nonempty K hne) a hsat





theorem sht_totalTurn_eq_four_of_eulerCharOne (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (h : EulerCharOne (ndt_StarHull K) a) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 :=
  ttf_totalTurn_eq_four_of_eulerCharOne K a (sht_starHull_period_ge_three K hK a) h





theorem sht_cornerBalance_eq_four_revCount (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    cornerBalance (ndt_StarHull K) a = 4 * revCount (ndt_StarHull K) a :=
  cornerBalance_eq_four_revCount (ndt_StarHull K) a

















theorem sht_contraction_of_not_saturating (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2) (hcK : c ∈ K)
    (hc : c ∉ bpc_orbitFootprint K a) :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a :=
  bpc_contraction_of_not_saturating K hK a c hcK hc







theorem sht_balancePreservingContraction_of_saturating
    (h : bpc_BalanceSaturatingContraction) : BalancePreservingContraction :=
  bpc_balancePreservingContraction_of_saturating h





theorem sht_unitCell_totalTurn_eq_four :
    totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 4 ∨
      totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 :=
  unitCell_turningIsFullRevolution



theorem sht_domino_totalTurn_eq_four :
    totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = 4 ∨
      totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = -4 :=
  domino_turningIsFullRevolution











































end Lattice

end StatMech
