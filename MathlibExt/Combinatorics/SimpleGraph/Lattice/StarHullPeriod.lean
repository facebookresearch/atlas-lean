/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHullFinite

/-!
# Boundary orbits have length at least three

A boundary orbit of a finite set of sites never returns to its starting dart after two steps of
`dartNext`: a case analysis over the three cases of the successor rule at each of the two steps
shows that the direction or the tail always changes. Since boundary orbits of finite sets have
length at least two, every boundary orbit of a finite set has length at least three. Combined with
the absence of diagonal touches, the face loops of boundary orbits of star hulls and of boxes are
cycles.

## Main results

* `StatMech.Lattice.shp_two_step_ne`: `dartNext K` has no orbit of length two.
* `StatMech.Lattice.shp_period_ge_three`: boundary orbits of a finite set have length at least
  three.
* `StatMech.Lattice.shp_starHull_orbit_isCycle`, `StatMech.Lattice.shp_box_orbit_isCycle`: the
  face loop of a boundary orbit of the star hull of a finite set, or of a box, is a cycle.
-/

@[expose] public section

open SimpleGraph Function Set Finset

namespace StatMech

namespace Lattice

/-- A dart direction plus its clockwise rotation is nonzero. -/
theorem shp_dir_add_t_ne_zero (e : Dart) : e.dir + (-rot90Fun e.dir) ≠ 0 := by
  intro h
  apply rot90Fun_dartDir_ne_dartDir e
  refine (?_ : e.dir = rot90Fun e.dir).symm
  funext i
  have hi := congrFun h i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hi
  omega

/-- Twice the clockwise rotation of a dart direction is nonzero. -/
theorem shp_two_t_ne_zero (e : Dart) :
    (-rot90Fun e.dir) + (-rot90Fun e.dir) ≠ (0 : Site 2) := by
  intro h
  apply neg_rot90Fun_dartDir_ne_zero e
  funext i
  have hi := congrFun h i
  simp only [Pi.add_apply, Pi.zero_apply] at hi
  change (-rot90Fun e.dir) i = (0 : Site 2) i
  simp only [Pi.zero_apply]
  omega

/-- The clockwise rotation of a dart direction minus that direction is nonzero. -/
theorem shp_t_sub_dir_ne_zero (e : Dart) :
    (-rot90Fun e.dir) + (-e.dir) ≠ (0 : Site 2) := by
  intro h
  apply neg_rot90Fun_dartDir_ne_dartDir e
  funext i
  have hi := congrFun h i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hi
  simp only [Pi.neg_apply]
  omega

/-- Rotating a dart direction clockwise twice reverses it. -/
theorem shp_neg_rot90_neg_rot90 (e : Dart) :
    (-rot90Fun (-rot90Fun e.dir) : Site 2) = -e.dir := by
  rw [rot90Fun_neg, rot90Fun_rot90Fun]; abel

/-- The boundary successor `dartNext K` has no point of period two: two steps never return a
dart to itself. -/
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
  · have hbt : (dartNext K e).tail = e.head + (-rot90Fun e.dir) := dartNext_right_tail K e hA1
    have hbd : (dartNext K e).dir = rot90Fun e.dir := (dartNext_front_head K e hA1).2
    by_cases hA2 : (dartNext K e).head + (-rot90Fun (dartNext K e).dir) ∈ K
    · rw [(dartNext_front_head K _ hA2).2, hbd, rot90Fun_rot90Fun] at hdir
      exact neg_dartDir_ne_dartDir e hdir
    · by_cases hB2 : (dartNext K e).tail + (-rot90Fun (dartNext K e).dir) ∈ K
      · rw [dartNext_straight_dir K _ hA2 hB2, hbd] at hdir
        exact rot90Fun_dartDir_ne_dartDir e hdir
      · rw [dartNext_left_tail K _ hA2 hB2, hbt, dart_head_eq e] at htail
        apply shp_dir_add_t_ne_zero e
        have : e.tail + (e.dir + (-rot90Fun e.dir)) = e.tail + 0 := by
          rw [add_zero, ← add_assoc]; exact htail
        exact add_left_cancel this
  · by_cases hB1 : e.tail + (-rot90Fun e.dir) ∈ K
    · have hbt : (dartNext K e).tail = e.tail + (-rot90Fun e.dir) :=
        dartNext_straight_tail K e hA1 hB1
      have hbd : (dartNext K e).dir = e.dir := dartNext_straight_dir K e hA1 hB1
      by_cases hA2 : (dartNext K e).head + (-rot90Fun (dartNext K e).dir) ∈ K
      · rw [(dartNext_front_head K _ hA2).2, hbd] at hdir
        exact rot90Fun_dartDir_ne_dartDir e hdir
      · by_cases hB2 : (dartNext K e).tail + (-rot90Fun (dartNext K e).dir) ∈ K
        · rw [dartNext_straight_tail K _ hA2 hB2, hbt, hbd] at htail
          apply shp_two_t_ne_zero e
          have : e.tail + ((-rot90Fun e.dir) + (-rot90Fun e.dir)) = e.tail + 0 := by
            rw [add_zero, ← add_assoc]; exact htail
          exact add_left_cancel this
        · rw [dartNext_left_dir K _ hA2 hB2, hbd] at hdir
          exact neg_rot90Fun_dartDir_ne_dartDir e hdir
    · have hbd : (dartNext K e).dir = -rot90Fun e.dir := dartNext_left_dir K e hA1 hB1
      have hbh : (dartNext K e).head = e.tail + (-rot90Fun e.dir) :=
        dartNext_left_head K e hA1 hB1
      by_cases hA2 : (dartNext K e).head + (-rot90Fun (dartNext K e).dir) ∈ K
      · rw [dartNext_right_tail K _ hA2, hbh, hbd, shp_neg_rot90_neg_rot90 e] at htail
        apply shp_t_sub_dir_ne_zero e
        have : e.tail + ((-rot90Fun e.dir) + (-e.dir)) = e.tail + 0 := by
          rw [add_zero, ← add_assoc]; exact htail
        exact add_left_cancel this
      · by_cases hB2 : (dartNext K e).tail + (-rot90Fun (dartNext K e).dir) ∈ K
        · rw [dartNext_straight_dir K _ hA2 hB2, hbd] at hdir
          exact neg_rot90Fun_dartDir_ne_dartDir e hdir
        · rw [dartNext_left_dir K _ hA2 hB2, hbd, shp_neg_rot90_neg_rot90 e] at hdir
          exact neg_dartDir_ne_dartDir e hdir

/-- No boundary orbit has length exactly two. -/
theorem shp_period_ne_two (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) : dartOrbitPeriod K a ≠ 2 := by
  intro h
  have hret : (dartNext K)^[2] a.1 = a.1 := by
    rw [← h]; exact orbit_iterate_period_eq K a
  exact shp_two_step_ne K a.1 hret

/-- Every boundary orbit of a finite set has length at least three. -/
theorem shp_period_ge_three (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : 3 ≤ dartOrbitPeriod K a := by
  have h2 : 1 < dartOrbitPeriod K a := one_lt_dartOrbitPeriod K hK a
  have hne : dartOrbitPeriod K a ≠ 2 := shp_period_ne_two K a
  omega

/-- Every boundary orbit of the star hull of a finite set has length at least three. -/
theorem shp_starHull_period_ge_three (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    3 ≤ dartOrbitPeriod (ndt_StarHull K) a :=
  shp_period_ge_three (ndt_StarHull K) (starHull_finite K hK) a

/-- The face loop of a boundary orbit of the star hull of a finite set is a cycle in the square
lattice. -/
theorem shp_starHull_orbit_isCycle (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    ((dartOrbitFaceWalk (ndt_StarHull K) a.1 a.2 (dartOrbitPeriod (ndt_StarHull K) a)).copy rfl
      (by rw [orbit_iterate_period_eq (ndt_StarHull K) a])).IsCycle :=
  ndt_orbit_isCycle K a (shp_starHull_period_ge_three K hK a)

/-- Every boundary orbit of the box `[-n, n]²` has length at least three. -/
theorem shp_box_period_ge_three (n : ℕ)
    (a : {e : Dart // IsBoundaryDart (box 2 n) e}) :
    3 ≤ dartOrbitPeriod (box 2 n) a :=
  shp_period_ge_three (box 2 n) (box_finite 2 n) a

/-- The face loop of a boundary orbit of the box `[-n, n]²` is a cycle. -/
theorem shp_box_orbit_isCycle (n : ℕ)
    (a : {e : Dart // IsBoundaryDart (box 2 n) e}) :
    ((dartOrbitFaceWalk (box 2 n) a.1 a.2 (dartOrbitPeriod (box 2 n) a)).copy rfl
      (by rw [orbit_iterate_period_eq (box 2 n) a])).IsCycle :=
  ndt_box_orbit_isCycle n a (shp_box_period_ge_three n a)

/-- The boundary orbit of a single site has length at least three (it has length four). -/
theorem shp_unitCell_period_ge_three : 3 ≤ dartOrbitPeriod unitCell ucBase := by
  rw [unitCell_orbitPeriod_eq_four]; norm_num

/-- The boundary orbit of a domino has length at least three (it has length six). -/
theorem shp_domino_period_ge_three : 3 ≤ dartOrbitPeriod domino dmBase := by
  rw [domino_orbitPeriod_eq_six]; norm_num

end Lattice

end StatMech
