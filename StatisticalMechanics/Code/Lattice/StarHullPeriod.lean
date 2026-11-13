/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.ContourLinksExits
import Code.Lattice.TurningNumber
import Code.Lattice.CornerBalance
import Code.Lattice.EarRemoval
import Code.Lattice.NoDiagTouchClose
import Code.Lattice.StarHullFinite

open SimpleGraph Function Set Finset

namespace StatMech

namespace Lattice









theorem shp_rot90_dir_ne (e : Dart) : rot90Fun e.dir ≠ e.dir := by
  rcases dartDir_cases e with hd | hd | hd | hd <;>
    rw [hd] <;> (intro h; have h0 := congrFun h 0; have h1 := congrFun h 1;
                 simp [rot90Fun] at h0 h1)



theorem shp_neg_rot90_dir_ne (e : Dart) : (-rot90Fun e.dir : Site 2) ≠ e.dir := by
  rcases dartDir_cases e with hd | hd | hd | hd <;>
    rw [hd] <;> (intro h; have h0 := congrFun h 0; have h1 := congrFun h 1;
                 simp [rot90Fun] at h0 h1)



theorem shp_neg_rot90_ne_zero (e : Dart) : (-rot90Fun e.dir : Site 2) ≠ 0 := by
  rcases dartDir_cases e with hd | hd | hd | hd <;>
    rw [hd] <;> (intro h; have h0 := congrFun h 0; have h1 := congrFun h 1;
                 simp [rot90Fun] at h0 h1)


theorem shp_neg_dir_ne_dir (e : Dart) : (-e.dir : Site 2) ≠ e.dir := by
  rcases dartDir_cases e with hd | hd | hd | hd <;>
    rw [hd] <;> (intro h; have h0 := congrFun h 0; have h1 := congrFun h 1;
                 simp at h0 h1)



theorem shp_dir_add_t_ne_zero (e : Dart) : e.dir + (-rot90Fun e.dir) ≠ 0 := by
  intro h
  apply shp_rot90_dir_ne e
  refine (?_ : e.dir = rot90Fun e.dir).symm
  funext i
  have hi := congrFun h i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hi
  omega



theorem shp_two_t_ne_zero (e : Dart) :
    (-rot90Fun e.dir) + (-rot90Fun e.dir) ≠ (0 : Site 2) := by
  intro h
  apply shp_neg_rot90_ne_zero e
  funext i
  have hi := congrFun h i
  simp only [Pi.add_apply, Pi.zero_apply] at hi
  change (-rot90Fun e.dir) i = (0 : Site 2) i
  simp only [Pi.zero_apply]
  omega



theorem shp_t_sub_dir_ne_zero (e : Dart) :
    (-rot90Fun e.dir) + (-e.dir) ≠ (0 : Site 2) := by
  intro h
  apply shp_neg_rot90_dir_ne e
  funext i
  have hi := congrFun h i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hi
  simp only [Pi.neg_apply]
  omega




theorem shp_neg_rot90_neg_rot90 (e : Dart) :
    (-rot90Fun (-rot90Fun e.dir) : Site 2) = -e.dir := by
  rw [rot90Fun_neg, rot90Fun_rot90Fun]; abel
















theorem shp_two_step_ne (K : Set (Site 2)) (e : Dart) :
    (dartNext K)^[2] e ≠ e := by
  classical
  have h2 : (dartNext K)^[2] e = dartNext K (dartNext K e) := by
    rw [Function.iterate_succ_apply', Function.iterate_one]
  rw [h2]
  intro hc
  have hdir : (dartNext K (dartNext K e)).dir = e.dir := congrArg Dart.dir hc
  have htail : (dartNext K (dartNext K e)).tail = e.tail := congrArg Dart.tail hc
  by_cases hA1 : e.head + (-rot90Fun e.dir) ∈ K
  · 
    have hbt : (dartNext K e).tail = e.head + (-rot90Fun e.dir) := dartNext_right_tail K e hA1
    have hbd : (dartNext K e).dir = rot90Fun e.dir := (dartNext_front_head K e hA1).2
    by_cases hA2 : (dartNext K e).head + (-rot90Fun (dartNext K e).dir) ∈ K
    · 
      rw [(dartNext_front_head K _ hA2).2, hbd, rot90Fun_rot90Fun] at hdir
      exact shp_neg_dir_ne_dir e hdir
    · by_cases hB2 : (dartNext K e).tail + (-rot90Fun (dartNext K e).dir) ∈ K
      · 
        rw [dartNext_straight_dir K _ hA2 hB2, hbd] at hdir
        exact shp_rot90_dir_ne e hdir
      · 
        rw [dartNext_left_tail K _ hA2 hB2, hbt, dart_head_eq e] at htail
        apply shp_dir_add_t_ne_zero e
        have : e.tail + (e.dir + (-rot90Fun e.dir)) = e.tail + 0 := by
          rw [add_zero, ← add_assoc]; exact htail
        exact add_left_cancel this
  · by_cases hB1 : e.tail + (-rot90Fun e.dir) ∈ K
    · 
      have hbt : (dartNext K e).tail = e.tail + (-rot90Fun e.dir) :=
        dartNext_straight_tail K e hA1 hB1
      have hbd : (dartNext K e).dir = e.dir := dartNext_straight_dir K e hA1 hB1
      by_cases hA2 : (dartNext K e).head + (-rot90Fun (dartNext K e).dir) ∈ K
      · 
        rw [(dartNext_front_head K _ hA2).2, hbd] at hdir
        exact shp_rot90_dir_ne e hdir
      · by_cases hB2 : (dartNext K e).tail + (-rot90Fun (dartNext K e).dir) ∈ K
        · 
          rw [dartNext_straight_tail K _ hA2 hB2, hbt, hbd] at htail
          apply shp_two_t_ne_zero e
          have : e.tail + ((-rot90Fun e.dir) + (-rot90Fun e.dir)) = e.tail + 0 := by
            rw [add_zero, ← add_assoc]; exact htail
          exact add_left_cancel this
        · 
          rw [dartNext_left_dir K _ hA2 hB2, hbd] at hdir
          exact shp_neg_rot90_dir_ne e hdir
    · 
      have hbd : (dartNext K e).dir = -rot90Fun e.dir := dartNext_left_dir K e hA1 hB1
      have hbh : (dartNext K e).head = e.tail + (-rot90Fun e.dir) := dartNext_left_head K e hA1 hB1
      by_cases hA2 : (dartNext K e).head + (-rot90Fun (dartNext K e).dir) ∈ K
      · 
        rw [dartNext_right_tail K _ hA2, hbh, hbd, shp_neg_rot90_neg_rot90 e] at htail
        apply shp_t_sub_dir_ne_zero e
        have : e.tail + ((-rot90Fun e.dir) + (-e.dir)) = e.tail + 0 := by
          rw [add_zero, ← add_assoc]; exact htail
        exact add_left_cancel this
      · by_cases hB2 : (dartNext K e).tail + (-rot90Fun (dartNext K e).dir) ∈ K
        · 
          rw [dartNext_straight_dir K _ hA2 hB2, hbd] at hdir
          exact shp_neg_rot90_dir_ne e hdir
        · 
          rw [dartNext_left_dir K _ hA2 hB2, hbd, shp_neg_rot90_neg_rot90 e] at hdir
          exact shp_neg_dir_ne_dir e hdir










theorem shp_period_ne_two (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) : dartOrbitPeriod K a ≠ 2 := by
  intro h
  have hret : (dartNext K)^[2] a.1 = a.1 := by
    rw [← h]; exact orbit_iterate_period_eq K a
  exact shp_two_step_ne K a.1 hret









theorem shp_period_ge_three (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : 3 ≤ dartOrbitPeriod K a := by
  have h2 : 1 < dartOrbitPeriod K a := one_lt_dartOrbitPeriod K hK a
  have hne : dartOrbitPeriod K a ≠ 2 := shp_period_ne_two K a
  omega














theorem shp_starHull_period_ge_three (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    3 ≤ dartOrbitPeriod (ndt_StarHull K) a :=
  shp_period_ge_three (ndt_StarHull K) (starHull_finite K hK) a




theorem shp_starHull_period_ge_three' (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    3 ≤ dartOrbitPeriod (ndt_StarHull K) a :=
  shp_period_ge_three (ndt_StarHull K) hSK a






theorem shp_starHull_orbit_isCycle (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    ((dartOrbitFaceWalk (ndt_StarHull K) a.1 a.2 (dartOrbitPeriod (ndt_StarHull K) a)).copy rfl
      (by rw [orbit_iterate_period_eq (ndt_StarHull K) a])).IsCycle :=
  ndt_orbit_isCycle K a (shp_starHull_period_ge_three K hK a)



theorem shp_box_period_ge_three (n : ℕ)
    (a : {e : Dart // IsBoundaryDart (box 2 n) e}) :
    3 ≤ dartOrbitPeriod (box 2 n) a :=
  shp_period_ge_three (box 2 n) (box_finite 2 n) a




theorem shp_box_orbit_isCycle (n : ℕ)
    (a : {e : Dart // IsBoundaryDart (box 2 n) e}) :
    ((dartOrbitFaceWalk (box 2 n) a.1 a.2 (dartOrbitPeriod (box 2 n) a)).copy rfl
      (by rw [orbit_iterate_period_eq (box 2 n) a])).IsCycle :=
  ndt_box_orbit_isCycle n a (shp_box_period_ge_three n a)









theorem shp_unitCell_period_ge_three : 3 ≤ dartOrbitPeriod unitCell ucBase := by
  rw [unitCell_orbitPeriod_eq_four]; norm_num




theorem shp_domino_period_ge_three : 3 ≤ dartOrbitPeriod domino dmBase := by
  rw [domino_orbitPeriod_eq_six]; norm_num
































end Lattice

end StatMech
