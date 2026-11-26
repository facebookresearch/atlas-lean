/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CornerBalanceUnprobedSite
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.UmlaufsatzBaseCases
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.GaussBonnet

/-!
# The lattice Umlaufsatz: total turn `±4`

The discrete Umlaufsatz (Hopf's rotation index theorem for lattice contours) says that the
boundary orbit of a finite nonempty set `K` of sites of `ℤ²` makes exactly one full revolution:
its total quarter-turn count over one period is `4` or `-4`, its total turning angle `±2π`.

This file proves:
* the arithmetic reduction: since the total turn is a multiple of `4`, it is `±4` as soon as its
  absolute value is at most `4` and it is nonzero (`uc_winds_iff`);
* invariance under the quarter-turn rotation `(x, y) ↦ (-y, x)` of `ℤ²`: rotating `K` rotates its
  boundary orbits and preserves period, corner counts and total turn;
* the base cases (unit cell, horizontal and vertical domino).

The lattice Umlaufsatz for general finite sets is not proved here: the only earlier derivation
went through the contraction hypothesis `bpc_BalanceSaturatingContraction`, which is false
(`not_bpc_BalanceSaturatingContraction` in `CornerBalanceUnprobedSite.lean`), and those
conditional theorems have been removed. Only the base cases and the reductions are genuine
results. The Umlaufsatz for simple closed lattice walks given by direction sequences is proved
unconditionally as `turnSum_eq_four_or_neg_four`; transferring it to boundary orbits would need the
face loop of the orbit to be a simple closed walk without U-turns.

## Main definitions

* `StatMech.Lattice.uc_WindsAtMostOnce`, `StatMech.Lattice.uc_WindsAtLeastOnce`: the total turn of
  the orbit has absolute value at most `4`, resp. is nonzero.
* `StatMech.Lattice.uc_rotSet`, `StatMech.Lattice.uc_rotDart`: the images of a set of sites and of
  a dart under the quarter-turn rotation.
* `StatMech.Lattice.uc_GeneralFullRevolution`, `StatMech.Lattice.uc_GeneralEulerCharOne`: the
  lattice Umlaufsatz for all finite nonempty sets, in turning and Euler-characteristic form.

## Main results

* `StatMech.Lattice.uc_winds_iff`: total turn `±4` iff at most one and at least one revolution.
* `StatMech.Lattice.uc_totalTurnAngle_eq_two_pi_iff`: total turn `±4` iff total angle `±2π`.
* `StatMech.Lattice.uc_cornerBalance_rot`, `StatMech.Lattice.uc_totalTurnZ_rot`: corner balance and
  total turn are invariant under the quarter-turn rotation.
* `StatMech.Lattice.uc_unitCell_totalTurnAngle_eq_two_pi`,
  `StatMech.Lattice.uc_domino_totalTurnAngle_eq_two_pi`,
  `StatMech.Lattice.uc_verticalDomino_totalTurn_eq_four`,
  `StatMech.Lattice.uc_verticalDomino_eulerCharOne`: the base cases.

## References

* H. Hopf, *Über die Drehung der Tangenten und Sehnen ebener Kurven*, Compositio Math. 2 (1935).
-/

@[expose] public section

open SimpleGraph Function Set

namespace StatMech

namespace Lattice

/-- The total turn of the boundary orbit of `a` over one period has absolute value at most `4`: the
orbit makes at most one full revolution. -/
def uc_WindsAtMostOnce (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ 4

/-- The total turn of the boundary orbit of `a` over one period is nonzero. -/
def uc_WindsAtLeastOnce (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  totalTurnZ K a.1 (dartOrbitPeriod K a) ≠ 0

/-- A total turn that is a multiple of `4`, nonzero and of absolute value at most `4` is `±4`. -/
theorem uc_totalTurn_eq_four_of_winds (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hmax : uc_WindsAtMostOnce K a) (hmin : uc_WindsAtLeastOnce K a) :
    totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
      totalTurnZ K a.1 (dartOrbitPeriod K a) = -4 := by
  have hdvd := four_dvd_orbit_totalTurnZ K a
  unfold uc_WindsAtMostOnce at hmax
  unfold uc_WindsAtLeastOnce at hmin
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

/-- Total turn `±4` satisfies both winding bounds. -/
theorem uc_winds_of_totalTurn_eq_four (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (h : totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
      totalTurnZ K a.1 (dartOrbitPeriod K a) = -4) :
    uc_WindsAtMostOnce K a ∧ uc_WindsAtLeastOnce K a := by
  unfold uc_WindsAtMostOnce uc_WindsAtLeastOnce
  rcases h with h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩

/-- Total turn `±4` holds exactly when the orbit winds at most once and at least once. -/
theorem uc_winds_iff (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (uc_WindsAtMostOnce K a ∧ uc_WindsAtLeastOnce K a) ↔
      (totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
        totalTurnZ K a.1 (dartOrbitPeriod K a) = -4) := by
  constructor
  · rintro ⟨hmax, hmin⟩; exact uc_totalTurn_eq_four_of_winds K a hmax hmin
  · exact uc_winds_of_totalTurn_eq_four K a

open Real in
/-- Total turn `±4` is equivalent to total turning angle `±2π`. -/
theorem uc_totalTurnAngle_eq_two_pi_iff (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (totalTurnAngle K a.1 (dartOrbitPeriod K a) = 2 * Real.pi ∨
        totalTurnAngle K a.1 (dartOrbitPeriod K a) = -(2 * Real.pi)) ↔
      (totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
        totalTurnZ K a.1 (dartOrbitPeriod K a) = -4) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [umBase_totalTurnAngle_eq]
  constructor
  · rintro (h | h)
    · left
      have : (totalTurnZ K a.1 (dartOrbitPeriod K a) : ℝ) = 4 := by
        have hh : (totalTurnZ K a.1 (dartOrbitPeriod K a) : ℝ) * (Real.pi / 2)
            = 4 * (Real.pi / 2) := by rw [h]; ring
        exact mul_right_cancel₀ (by positivity) hh
      exact_mod_cast this
    · right
      have : (totalTurnZ K a.1 (dartOrbitPeriod K a) : ℝ) = -4 := by
        have hh : (totalTurnZ K a.1 (dartOrbitPeriod K a) : ℝ) * (Real.pi / 2)
            = (-4) * (Real.pi / 2) := by rw [h]; ring
        exact mul_right_cancel₀ (by positivity) hh
      exact_mod_cast this
  · rintro (h | h)
    · left; rw [h]; push_cast; ring
    · right; rw [h]; push_cast; ring

open Real in
/-- The unit-cell orbit has total turning angle `±2π` (in fact `-2π`). -/
theorem uc_unitCell_totalTurnAngle_eq_two_pi :
    totalTurnAngle unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 2 * Real.pi ∨
      totalTurnAngle unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -(2 * Real.pi) :=
  Or.inr umBase_square_turning_period

/-- The unit-cell orbit winds exactly once. -/
theorem uc_unitCell_winds :
    uc_WindsAtMostOnce unitCell ucBase ∧ uc_WindsAtLeastOnce unitCell ucBase :=
  uc_winds_of_totalTurn_eq_four unitCell ucBase unitCell_turningIsFullRevolution

open Real in
/-- The domino orbit has total turning angle `±2π` (in fact `-2π`). -/
theorem uc_domino_totalTurnAngle_eq_two_pi :
    totalTurnAngle domino dmBase.1 (dartOrbitPeriod domino dmBase) = 2 * Real.pi ∨
      totalTurnAngle domino dmBase.1 (dartOrbitPeriod domino dmBase) = -(2 * Real.pi) := by
  right
  rw [show (dmBase).1 = dmD0 from rfl, domino_orbitPeriod_eq_six]
  exact umBase_domino_turning

/-- The domino orbit winds exactly once. -/
theorem uc_domino_winds :
    uc_WindsAtMostOnce domino dmBase ∧ uc_WindsAtLeastOnce domino dmBase :=
  uc_winds_of_totalTurn_eq_four domino dmBase domino_turningIsFullRevolution

/-- Winding at most once and at least once is `TurningIsFullRevolution`. -/
theorem uc_winds_iff_turningIsFullRevolution (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (uc_WindsAtMostOnce K a ∧ uc_WindsAtLeastOnce K a) ↔ TurningIsFullRevolution K a := by
  rw [uc_winds_iff]; rfl

/-- The quarter-turn rotation `(x, y) ↦ (-y, x)` of `ℤ²` is additive. -/
theorem uc_rot90Fun_add (x y : Site 2) : rot90Fun (x + y) = rot90Fun x + rot90Fun y := by
  funext i
  fin_cases i
  · change -(x + y) 1 = -x 1 + -y 1
    rw [Pi.add_apply]; ring
  · change (x + y) 0 = x 0 + y 0
    rw [Pi.add_apply]

/-- The image of a set of sites under the quarter-turn rotation. -/
noncomputable def uc_rotSet (K : Set (Site 2)) : Set (Site 2) := rot90Fun '' K

/-- `rot90Fun z` lies in the rotated set iff `z` lies in the original set. -/
theorem uc_rotSet_mem_iff (K : Set (Site 2)) (z : Site 2) :
    rot90Fun z ∈ uc_rotSet K ↔ z ∈ K := by
  unfold uc_rotSet
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyz : y = z := rot90Fun_injective hxy
    rwa [hyz] at hy
  · intro h; exact ⟨z, h, rfl⟩

/-- The image of a dart under the quarter-turn rotation. -/
noncomputable def uc_rotDart (e : Dart) : Dart :=
  mkDart (rot90Fun e.tail) (rot90Fun e.dir) (unitWt_rot90Fun_dir e)

@[simp] theorem uc_rotDart_tail (e : Dart) : (uc_rotDart e).tail = rot90Fun e.tail := rfl

@[simp] theorem uc_rotDart_dir (e : Dart) : (uc_rotDart e).dir = rot90Fun e.dir := by
  rw [uc_rotDart, mkDart_dir]

@[simp] theorem uc_rotDart_head (e : Dart) : (uc_rotDart e).head = rot90Fun e.head := by
  rw [uc_rotDart, mkDart_head, Dart.dir_def, sub_eq_add_neg, uc_rot90Fun_add, rot90Fun_neg]; abel

/-- Rotation of darts is injective. -/
theorem uc_rotDart_injective : Function.Injective uc_rotDart := by
  intro a b h
  apply dart_eq_of_tail_dir
  · exact rot90Fun_injective (by
      have := congrArg Dart.tail h; simpa only [uc_rotDart_tail] using this)
  · exact rot90Fun_injective (by
      have := congrArg Dart.dir h; simpa only [uc_rotDart_dir] using this)

/-- The turn at a rotated dart of the rotated set equals the turn at the original dart. -/
theorem uc_turnZ_rot (K : Set (Site 2)) (e : Dart) :
    turnZ (uc_rotSet K) (uc_rotDart e) = turnZ K e := by
  classical
  unfold turnZ
  rw [uc_rotDart_head, uc_rotDart_dir, uc_rotDart_tail]
  have m1 : (rot90Fun e.head + -rot90Fun (rot90Fun e.dir) ∈ uc_rotSet K) ↔
            (e.head + -rot90Fun e.dir ∈ K) := by
    rw [show rot90Fun e.head + -rot90Fun (rot90Fun e.dir)
        = rot90Fun (e.head + -rot90Fun e.dir) by rw [uc_rot90Fun_add, rot90Fun_neg]]
    exact uc_rotSet_mem_iff K _
  have m2 : (rot90Fun e.tail + -rot90Fun (rot90Fun e.dir) ∈ uc_rotSet K) ↔
            (e.tail + -rot90Fun e.dir ∈ K) := by
    rw [show rot90Fun e.tail + -rot90Fun (rot90Fun e.dir)
        = rot90Fun (e.tail + -rot90Fun e.dir) by rw [uc_rot90Fun_add, rot90Fun_neg]]
    exact uc_rotSet_mem_iff K _
  by_cases h1 : e.head + -rot90Fun e.dir ∈ K
  · rw [ite_eq_left (m1.mpr h1), ite_eq_left h1]
  · rw [ite_eq_right (fun hh => h1 (m1.mp hh)), ite_eq_right h1]
    by_cases h2 : e.tail + -rot90Fun e.dir ∈ K
    · rw [ite_eq_left (m2.mpr h2), ite_eq_left h2]
    · rw [ite_eq_right (fun hh => h2 (m2.mp hh)), ite_eq_right h2]

/-- Rotation commutes with the successor map: the successor of a rotated dart in the rotated set is
the rotation of the successor. -/
theorem uc_dartNext_rot (K : Set (Site 2)) (e : Dart) :
    dartNext (uc_rotSet K) (uc_rotDart e) = uc_rotDart (dartNext K e) := by
  classical
  have m1 : ((uc_rotDart e).head + -rot90Fun (uc_rotDart e).dir ∈ uc_rotSet K) ↔
            (e.head + -rot90Fun e.dir ∈ K) := by
    rw [uc_rotDart_head, uc_rotDart_dir,
        show rot90Fun e.head + -rot90Fun (rot90Fun e.dir)
        = rot90Fun (e.head + -rot90Fun e.dir) by rw [uc_rot90Fun_add, rot90Fun_neg]]
    exact uc_rotSet_mem_iff K _
  have m2 : ((uc_rotDart e).tail + -rot90Fun (uc_rotDart e).dir ∈ uc_rotSet K) ↔
            (e.tail + -rot90Fun e.dir ∈ K) := by
    rw [uc_rotDart_tail, uc_rotDart_dir,
        show rot90Fun e.tail + -rot90Fun (rot90Fun e.dir)
        = rot90Fun (e.tail + -rot90Fun e.dir) by rw [uc_rot90Fun_add, rot90Fun_neg]]
    exact uc_rotSet_mem_iff K _
  by_cases h1 : e.head + -rot90Fun e.dir ∈ K
  · rw [dartNext_of_front_mem (uc_rotSet K) (uc_rotDart e) (m1.mpr h1),
        dartNext_of_front_mem K e h1]
    apply dart_eq_of_tail_dir
    · simp only [mkDart_tail, uc_rotDart_head, uc_rotDart_dir, uc_rotDart_tail]
      rw [uc_rot90Fun_add, rot90Fun_neg]
    · simp only [mkDart_dir, uc_rotDart_dir]
  · by_cases h2 : e.tail + -rot90Fun e.dir ∈ K
    · rw [dartNext_of_side_mem (uc_rotSet K) (uc_rotDart e) (fun hh => h1 (m1.mp hh)) (m2.mpr h2),
          dartNext_of_side_mem K e h1 h2]
      apply dart_eq_of_tail_dir
      · simp only [mkDart_tail, uc_rotDart_tail, uc_rotDart_dir]
        rw [uc_rot90Fun_add, rot90Fun_neg]
      · simp only [mkDart_dir, uc_rotDart_dir]
    · rw [dartNext_of_corner (uc_rotSet K) (uc_rotDart e) (fun hh => h1 (m1.mp hh))
            (fun hh => h2 (m2.mp hh)),
          dartNext_of_corner K e h1 h2]
      apply dart_eq_of_tail_dir
      · simp only [mkDart_tail, uc_rotDart_tail]
      · simp only [mkDart_dir, uc_rotDart_dir]; rw [rot90Fun_neg]

/-- Rotation commutes with every iterate of the successor map. -/
theorem uc_iterate_dartNext_rot (K : Set (Site 2)) (e : Dart) (k : ℕ) :
    (dartNext (uc_rotSet K))^[k] (uc_rotDart e) = uc_rotDart ((dartNext K)^[k] e) := by
  induction k generalizing e with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, uc_dartNext_rot, ih]

/-- The rotation of a boundary dart of `K` is a boundary dart of the rotated set. -/
theorem uc_rotDart_boundary (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) :
    IsBoundaryDart (uc_rotSet K) (uc_rotDart e) := by
  refine ⟨?_, ?_⟩
  · rw [uc_rotDart_tail, uc_rotSet_mem_iff]; exact he.1
  · rw [uc_rotDart_head, uc_rotSet_mem_iff]; exact he.2

/-- Rotation preserves the number of corners with turn `1`. -/
theorem uc_rightCornerCount_rot (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    rightCornerCount (uc_rotSet K) (uc_rotDart e) p = rightCornerCount K e p := by
  classical
  unfold rightCornerCount
  congr 2
  apply Finset.filter_congr
  intro i _
  rw [uc_iterate_dartNext_rot, uc_turnZ_rot]

/-- Rotation preserves the number of corners with turn `-1`. -/
theorem uc_leftCornerCount_rot (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    leftCornerCount (uc_rotSet K) (uc_rotDart e) p = leftCornerCount K e p := by
  classical
  unfold leftCornerCount
  congr 2
  apply Finset.filter_congr
  intro i _
  rw [uc_iterate_dartNext_rot, uc_turnZ_rot]

/-- Rotation as a map from boundary darts of `K` to boundary darts of the rotated set. -/
noncomputable def uc_rotSub (K : Set (Site 2)) :
    {e : Dart // IsBoundaryDart K e} → {e : Dart // IsBoundaryDart (uc_rotSet K) e} :=
  fun a => ⟨uc_rotDart a.1, uc_rotDart_boundary K a.1 a.2⟩

@[simp] theorem uc_rotSub_val (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (uc_rotSub K a).1 = uc_rotDart a.1 := rfl

/-- Rotation preserves periodic points of the successor map on boundary darts. -/
theorem uc_isPeriodicPt_rot (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    Function.IsPeriodicPt (dartNextSub (uc_rotSet K)) n (uc_rotSub K a) ↔
      Function.IsPeriodicPt (dartNextSub K) n a := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  constructor
  · intro h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    rw [dartNextSub_iterate_val] at hv
    change ((dartNextSub K)^[n] a).1 = a.1
    rw [dartNextSub_iterate_val]
    have hstep : (dartNext (uc_rotSet K))^[n] (uc_rotSub K a).1
        = uc_rotDart ((dartNext K)^[n] a.1) := by
      change (dartNext (uc_rotSet K))^[n] (uc_rotDart a.1) = _
      rw [uc_iterate_dartNext_rot]
    rw [hstep] at hv
    exact uc_rotDart_injective hv
  · intro h
    apply Subtype.ext
    rw [dartNextSub_iterate_val]
    change (dartNext (uc_rotSet K))^[n] (uc_rotDart a.1) = uc_rotDart a.1
    rw [uc_iterate_dartNext_rot]
    have hv := congrArg Subtype.val h
    rw [dartNextSub_iterate_val] at hv
    rw [hv]

/-- Rotation preserves the orbit period. -/
theorem uc_dartOrbitPeriod_rot (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    dartOrbitPeriod (uc_rotSet K) (uc_rotSub K a) = dartOrbitPeriod K a := by
  unfold dartOrbitPeriod
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  exact uc_isPeriodicPt_rot K a n

/-- Rotation preserves the corner balance of a boundary orbit. -/
theorem uc_cornerBalance_rot (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    cornerBalance (uc_rotSet K) (uc_rotSub K a) = cornerBalance K a := by
  unfold cornerBalance
  rw [uc_rotSub_val, uc_dartOrbitPeriod_rot, uc_rightCornerCount_rot, uc_leftCornerCount_rot]

/-- Rotation preserves the total turn of a boundary orbit. -/
theorem uc_totalTurnZ_rot (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnZ (uc_rotSet K) (uc_rotSub K a).1 (dartOrbitPeriod (uc_rotSet K) (uc_rotSub K a))
      = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
  rw [← cornerBalance_eq_totalTurnZ, ← cornerBalance_eq_totalTurnZ, uc_cornerBalance_rot]

/-- If a boundary orbit makes one full revolution, so does its rotation. -/
theorem uc_turningIsFullRevolution_rot (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : TurningIsFullRevolution K a) :
    TurningIsFullRevolution (uc_rotSet K) (uc_rotSub K a) := by
  unfold TurningIsFullRevolution at h ⊢
  rw [uc_totalTurnZ_rot]
  exact h

/-- The rotated domino is the vertical domino `{(0, 0), (0, 1)}`. -/
theorem uc_rotSet_domino : uc_rotSet domino = {![0, 0], ![0, 1]} := by
  unfold uc_rotSet domino
  rw [Set.image_insert_eq, Set.image_singleton,
      show rot90Fun (![0, 0] : Site 2) = ![0, 0] by
        rw [rot90Fun_apply]; funext i; fin_cases i <;> simp,
      show rot90Fun (![1, 0] : Site 2) = ![0, 1] by
        rw [rot90Fun_apply]; funext i; fin_cases i <;> simp]

/-- The vertical domino orbit has total turn `±4`. -/
theorem uc_verticalDomino_totalTurn_eq_four :
    totalTurnZ (uc_rotSet domino) (uc_rotSub domino dmBase).1
        (dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase)) = 4 ∨
      totalTurnZ (uc_rotSet domino) (uc_rotSub domino dmBase).1
        (dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase)) = -4 := by
  rw [uc_totalTurnZ_rot]
  exact domino_turningIsFullRevolution

open Real in
/-- The vertical domino orbit has total turning angle `±2π`. -/
theorem uc_verticalDomino_totalTurnAngle_eq_two_pi :
    totalTurnAngle (uc_rotSet domino) (uc_rotSub domino dmBase).1
        (dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase)) = 2 * Real.pi ∨
      totalTurnAngle (uc_rotSet domino) (uc_rotSub domino dmBase).1
        (dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase)) = -(2 * Real.pi) := by
  rw [umBase_totalTurnAngle_eq]
  rcases uc_verticalDomino_totalTurn_eq_four with h | h
  · left; rw [h]; push_cast; ring
  · right; rw [h]; push_cast; ring

/-- The lattice Umlaufsatz for all finite nonempty sets: every boundary orbit has total turn `±4`.
Not proved in this library. -/
def uc_GeneralFullRevolution : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → K.Nonempty →
    ∀ (a : {e : Dart // IsBoundaryDart K e}), TurningIsFullRevolution K a

/-- Every boundary orbit of every finite nonempty set satisfies `EulerCharOne`. Not proved in this
library. -/
def uc_GeneralEulerCharOne : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → K.Nonempty →
    ∀ (a : {e : Dart // IsBoundaryDart K e}), EulerCharOne K a

/-- The vertical domino orbit satisfies `EulerCharOne`. -/
theorem uc_verticalDomino_eulerCharOne :
    EulerCharOne (uc_rotSet domino) (uc_rotSub domino dmBase) := by
  have hrev : TurningIsFullRevolution (uc_rotSet domino) (uc_rotSub domino dmBase) :=
    uc_verticalDomino_totalTurn_eq_four
  have hp : 3 ≤ dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase) := by
    have := orbitPeriod_ge_four_of_fullRevolution (uc_rotSet domino) (uc_rotSub domino dmBase) hrev
    omega
  exact (eulerCharOne_iff_turningIsFullRevolution (uc_rotSet domino) (uc_rotSub domino dmBase)
    hp).mpr hrev

end Lattice

end StatMech
