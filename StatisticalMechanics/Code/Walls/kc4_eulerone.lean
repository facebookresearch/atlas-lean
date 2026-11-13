/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































import Mathlib
import Code.Lattice.Cyclomatic
import Code.Lattice.EulerFaces2
import Code.Lattice.JordanEulerSeparation
import Code.Lattice.JordanCycleSpace
import Code.Lattice.GaussBonnet
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.NoDiagTouchClose
import Code.Walls.jwd_contoureulerone

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice













theorem kc4_cycleGraph_nullity_one (n : ℕ) : nullity (cycleGraph (n + 3)) = 1 := by
  unfold nullity
  have hc : Nat.card (cycleGraph (n + 3)).ConnectedComponent = 1 :=
    card_components_eq_one_of_connected cycleGraph_connected
  have he : (cycleGraph (n + 3)).edgeSet.ncard = n + 3 := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset, cycleGraph_card_edges]
  rw [hc, he]
  simp [Nat.card_eq_fintype_card]





theorem kc4_cycleGraph_cyclomaticNumber_one (n : ℕ) :
    cyclomaticNumber (cycleGraph (n + 3)) = 1 := by
  unfold cyclomaticNumber
  rw [cycleGraph_card_edges n]
  simp




theorem kc4_cycleGraph_boundedFaceCount_two (n : ℕ) :
    faceCount (cycleGraph (n + 3)) = 2 := by
  rw [faceCount, kc4_cycleGraph_nullity_one]













noncomputable def kc4_contourEulerChar (p : ℕ) : ℕ := contourEulerChar p














theorem kc4_eulerOne {p : ℕ} (hp : 3 ≤ p) : kc4_contourEulerChar p = 1 := by
  unfold kc4_contourEulerChar contourEulerChar
  rw [if_pos hp]
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 3 := ⟨p - 3, by omega⟩
  exact kc4_cycleGraph_cyclomaticNumber_one n



theorem kc4_eulerOne_cycleGraph (n : ℕ) :
    kc4_contourEulerChar (n + 3) = cyclomaticNumber (cycleGraph (n + 3)) := by
  unfold kc4_contourEulerChar contourEulerChar
  rw [if_pos (by omega)]




























theorem kc4_orbitLoop_nullity_one (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1))
      (Set.Iio (dartOrbitPeriod K a))) :
    nullity (mpl_orbitLoop K a).toSubgraph.coe = 1 :=
  jcs_cycle_nullity_eq_one _ (mpl_orbitLoop_isCycle K a hp hinj)





theorem kc4_orbitLoop_boundedFaceCount_two (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1))
      (Set.Iio (dartOrbitPeriod K a))) :
    faceCount (mpl_orbitLoop K a).toSubgraph.coe = 2 :=
  jcs_cycle_faceCount_eq_two _ (mpl_orbitLoop_isCycle K a hp hinj)





















theorem kc4_box_orbitLoop_nullity_one (n : ℕ) (a : {e : Dart // IsBoundaryDart (box 2 n) e})
    (hp : 3 ≤ dartOrbitPeriod (box 2 n) a) :
    nullity (((dartOrbitFaceWalk (box 2 n) a.1 a.2
      (dartOrbitPeriod (box 2 n) a)).copy rfl
      (by rw [orbit_iterate_period_eq (box 2 n) a]))).toSubgraph.coe = 1 :=
  jcs_cycle_nullity_eq_one _ (ndt_box_orbit_isCycle n a hp)




theorem kc4_box_orbitLoop_boundedFaceCount_two (n : ℕ)
    (a : {e : Dart // IsBoundaryDart (box 2 n) e})
    (hp : 3 ≤ dartOrbitPeriod (box 2 n) a) :
    faceCount (((dartOrbitFaceWalk (box 2 n) a.1 a.2
      (dartOrbitPeriod (box 2 n) a)).copy rfl
      (by rw [orbit_iterate_period_eq (box 2 n) a]))).toSubgraph.coe = 2 :=
  jcs_cycle_faceCount_eq_two _ (ndt_box_orbit_isCycle n a hp)







theorem kc4_contourEulerChar_eq_jwd (p : ℕ) :
    kc4_contourEulerChar p = contourEulerChar p := rfl



theorem kc4_eulerOne_eq_jwd {p : ℕ} (hp : 3 ≤ p) :
    kc4_contourEulerChar p = contourEulerChar p ∧ kc4_contourEulerChar p = 1 :=
  ⟨rfl, kc4_eulerOne hp⟩

end Walls

end StatMech
