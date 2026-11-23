/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.DartOrbit
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.ZMod.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring.RingNF

/-!
# Turning of boundary-tracing orbits on the square lattice

For a set `K` of sites of `ℤ²`, the boundary darts of `K` (directed lattice edges from a site of
`K` to a site outside `K`) are permuted by the boundary-tracing successor `dartNext K`. This file
measures how much the direction of a dart turns along such an orbit, in quarter turns.

At each step the direction rotates by `rotPow (turn K e)`, a power of the counterclockwise
quarter-turn `rot90Fun`; `turnZ K e ∈ {1, 0, -1}` is the same turn as a signed integer
(`+1` counterclockwise, `0` straight, `-1` clockwise). Along a closed orbit the direction
returns to itself, so the total signed turning `totalTurnZ` is a multiple of `4`; it is also
bounded in absolute value by the orbit length.

## Main definitions

* `StatMech.Lattice.rotPow`: rotation of `ℤ²` by `s : ZMod 4` quarter turns.
* `StatMech.Lattice.turn`, `StatMech.Lattice.turnZ`: the quarter turn from `e` to `dartNext K e`.
* `StatMech.Lattice.cumTurn`, `StatMech.Lattice.totalTurnZ`: cumulative turning along an orbit.
* `StatMech.Lattice.TurningIsFullRevolution`: the total turning around an orbit is `±4`.

## Main results

* `StatMech.Lattice.dir_iterate_eq_rotPow_cumTurn`: the direction after `k` steps is the initial
  direction rotated by the cumulative turn.
* `StatMech.Lattice.four_dvd_orbit_totalTurnZ`: the total turning around an orbit is divisible
  by `4`.
* `StatMech.Lattice.abs_orbit_totalTurnZ_le`: it is at most the orbit length in absolute value.
* `StatMech.Lattice.orbitPeriod_ge_four_of_fullRevolution`: an orbit making a full revolution has
  length at least `4`.

That a boundary orbit of a finite set makes exactly one full revolution (the discrete
Umlaufsatz) is proved for direction sequences in
`MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.UmlaufsatzFinal` and
`PhyslibExt.CondensedMatter.IsingModel.Onsager.GeneralUmlaufsatz`.
-/

@[expose] public section

open SimpleGraph Function

namespace StatMech

namespace Lattice

/-- Four counterclockwise quarter turns are the identity, i.e. every site is a periodic point of
  `rot90Fun` of period `4`. -/
theorem rot90Fun_iterate_four_eq (x : Site 2) : rot90Fun^[4] x = x := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  exact rot90Fun_four x

/-- Rotation of `ℤ²` by `s` counterclockwise quarter turns, `s : ZMod 4`. -/
noncomputable def rotPow (s : ZMod 4) (x : Site 2) : Site 2 := rot90Fun^[s.val] x

@[simp] theorem rotPow_zero (x : Site 2) : rotPow 0 x = x := rfl

@[simp] theorem rotPow_one (x : Site 2) : rotPow 1 x = rot90Fun x := rfl

theorem rotPow_two (x : Site 2) : rotPow 2 x = -x := by
  change rot90Fun^[(2 : ZMod 4).val] x = -x
  have h : (2 : ZMod 4).val = 2 := by decide
  rw [h]; exact rot90Fun_rot90Fun x

theorem rotPow_three (x : Site 2) : rotPow 3 x = -rot90Fun x := by
  change rot90Fun^[(3 : ZMod 4).val] x = -rot90Fun x
  have h : (3 : ZMod 4).val = 3 := by decide
  rw [h]; change rot90Fun (rot90Fun (rot90Fun x)) = -rot90Fun x
  rw [rot90Fun_rot90Fun]

/-- `rotPow` is an action of the additive group `ZMod 4`. -/
theorem rotPow_add (a b : ZMod 4) (x : Site 2) :
    rotPow (a + b) x = rotPow a (rotPow b x) := by
  have hp : Function.IsPeriodicPt rot90Fun 4 x := rot90Fun_iterate_four_eq x
  unfold rotPow
  rw [← Function.iterate_add_apply, ZMod.val_add, hp.iterate_mod_apply]

theorem neg_dartDir_ne_dartDir (e : Dart) : -e.dir ≠ e.dir := by
  intro h
  apply dartDir_ne_zero e
  funext i
  have hi := congrFun h i
  simp only [Pi.neg_apply, Pi.zero_apply] at hi ⊢
  omega

theorem zmod4_cases (s : ZMod 4) : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by decide +revert

/-- A nontrivial rotation moves every lattice direction: `rotPow s` fixes the direction of a dart
  only for `s = 0`. -/
theorem rotPow_dir_eq_iff (e : Dart) (s : ZMod 4) :
    rotPow s e.dir = e.dir ↔ s = 0 := by
  constructor
  · intro h
    rcases zmod4_cases s with h0 | h1 | h2 | h3
    · exact h0
    · subst h1; rw [rotPow_one] at h; exact absurd h (rot90Fun_dartDir_ne_dartDir e)
    · subst h2; rw [rotPow_two] at h; exact absurd h (neg_dartDir_ne_dartDir e)
    · subst h3; rw [rotPow_three] at h; exact absurd h (neg_rot90Fun_dartDir_ne_dartDir e)
  · rintro rfl; rfl

/-- The quarter turn, as an element of `ZMod 4`, from the boundary dart `e` of `K` to its successor
  `dartNext K e`: `1` for a counterclockwise (left) turn, `0` for going straight, `3` for a
  clockwise (right) turn. -/
noncomputable def turn (K : Set (Site 2)) (e : Dart) : ZMod 4 := by
  classical
  exact
    if e.head + (-rot90Fun e.dir) ∈ K then 1
    else if e.tail + (-rot90Fun e.dir) ∈ K then 0
    else 3

/-- The signed quarter turn from `e` to `dartNext K e`: `1` counterclockwise, `0` straight, `-1`
  clockwise. Its reduction mod `4` is `turn K e`. -/
noncomputable def turnZ (K : Set (Site 2)) (e : Dart) : ℤ := by
  classical
  exact
    if e.head + (-rot90Fun e.dir) ∈ K then 1
    else if e.tail + (-rot90Fun e.dir) ∈ K then 0
    else -1

theorem turnZ_mem (K : Set (Site 2)) (e : Dart) :
    turnZ K e = 1 ∨ turnZ K e = 0 ∨ turnZ K e = -1 := by
  classical
  unfold turnZ
  split_ifs <;> simp

theorem abs_turnZ_le_one (K : Set (Site 2)) (e : Dart) : |turnZ K e| ≤ 1 := by
  rcases turnZ_mem K e with h | h | h <;> rw [h] <;> decide

theorem turnZ_cast_eq_turn (K : Set (Site 2)) (e : Dart) :
    ((turnZ K e : ℤ) : ZMod 4) = turn K e := by
  classical
  unfold turnZ turn
  split_ifs <;> decide

/-- The direction of `dartNext K e` is the direction of `e` rotated by `turn K e` quarter turns. -/
theorem dartNext_dir_eq_rotPow_turn (K : Set (Site 2)) (e : Dart) :
    (dartNext K e).dir = rotPow (turn K e) e.dir := by
  classical
  unfold turn
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [ite_eq_left hA, (dartNext_front_head K e hA).2]; rfl
  · rw [ite_eq_right hA]
    by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [ite_eq_left hB, dartNext_straight_dir K e hA hB]; rfl
    · rw [ite_eq_right hB, dartNext_left_dir K e hA hB, rotPow_three]

/-- The cumulative turn, in `ZMod 4`, over the first `k` steps of the `dartNext K`-orbit of `e`. -/
noncomputable def cumTurn (K : Set (Site 2)) (e : Dart) (k : ℕ) : ZMod 4 :=
  ∑ i ∈ Finset.range k, turn K ((dartNext K)^[i] e)

@[simp] theorem cumTurn_zero (K : Set (Site 2)) (e : Dart) : cumTurn K e 0 = 0 := by
  simp [cumTurn]

theorem cumTurn_succ (K : Set (Site 2)) (e : Dart) (k : ℕ) :
    cumTurn K e (k + 1) = turn K ((dartNext K)^[k] e) + cumTurn K e k := by
  unfold cumTurn; rw [Finset.sum_range_succ]; ring

/-- After `k` boundary-tracing steps the direction of a dart is its initial direction rotated by the
  cumulative turn `cumTurn K e k`. -/
theorem dir_iterate_eq_rotPow_cumTurn (K : Set (Site 2)) (e : Dart) (k : ℕ) :
    ((dartNext K)^[k] e).dir = rotPow (cumTurn K e k) e.dir := by
  induction k with
  | zero => rw [cumTurn_zero, rotPow_zero, Function.iterate_zero_apply]
  | succ n ih =>
    rw [Function.iterate_succ_apply', dartNext_dir_eq_rotPow_turn, ih, cumTurn_succ,
      rotPow_add]

/-- The total signed turning (in quarter turns) over the first `p` steps of the `dartNext K`-orbit
  of `e`. -/
noncomputable def totalTurnZ (K : Set (Site 2)) (e : Dart) (p : ℕ) : ℤ :=
  ∑ i ∈ Finset.range p, turnZ K ((dartNext K)^[i] e)

@[simp] theorem totalTurnZ_zero (K : Set (Site 2)) (e : Dart) : totalTurnZ K e 0 = 0 := by
  simp [totalTurnZ]

theorem totalTurnZ_cast_eq_cumTurn (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    ((totalTurnZ K e p : ℤ) : ZMod 4) = cumTurn K e p := by
  unfold totalTurnZ cumTurn
  push_cast
  exact Finset.sum_congr rfl (fun i _ => turnZ_cast_eq_turn K _)

theorem abs_totalTurnZ_le (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    |totalTurnZ K e p| ≤ (p : ℤ) := by
  unfold totalTurnZ
  calc |∑ i ∈ Finset.range p, turnZ K ((dartNext K)^[i] e)|
      ≤ ∑ i ∈ Finset.range p, |turnZ K ((dartNext K)^[i] e)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range p, (1 : ℤ) :=
        Finset.sum_le_sum (fun i _ => abs_turnZ_le_one K _)
    _ = (p : ℤ) := by simp

theorem cumTurn_eq_zero_of_iterate_eq (K : Set (Site 2)) (e : Dart) (p : ℕ)
    (hp : (dartNext K)^[p] e = e) : cumTurn K e p = 0 := by
  have hdir : ((dartNext K)^[p] e).dir = e.dir := by rw [hp]
  rw [dir_iterate_eq_rotPow_cumTurn] at hdir
  exact (rotPow_dir_eq_iff e (cumTurn K e p)).mp hdir

/-- If the orbit of `e` closes after `p` steps, the total signed turning over these steps is
  divisible by `4`. -/
theorem four_dvd_totalTurnZ_of_iterate_eq (K : Set (Site 2)) (e : Dart) (p : ℕ)
    (hp : (dartNext K)^[p] e = e) : (4 : ℤ) ∣ totalTurnZ K e p := by
  have hz : ((totalTurnZ K e p : ℤ) : ZMod 4) = 0 := by
    rw [totalTurnZ_cast_eq_cumTurn]; exact cumTurn_eq_zero_of_iterate_eq K e p hp
  have hdvd : ((4 : ℕ) : ℤ) ∣ totalTurnZ K e p :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp hz
  exact_mod_cast hdvd

theorem orbit_iterate_period_eq (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (dartNext K)^[dartOrbitPeriod K a] a.1 = a.1 := by
  have h := dartOrbitPeriod_iterate K a
  have h2 := congrArg Subtype.val h
  rwa [dartNextSub_iterate_val] at h2

theorem dartOrbitPeriod_cumTurn_eq_zero (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    cumTurn K a.1 (dartOrbitPeriod K a) = 0 :=
  cumTurn_eq_zero_of_iterate_eq K a.1 (dartOrbitPeriod K a) (orbit_iterate_period_eq K a)

/-- The total signed turning around a boundary orbit, taken over its minimal period, is divisible by
  `4`. -/
theorem four_dvd_orbit_totalTurnZ (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (4 : ℤ) ∣ totalTurnZ K a.1 (dartOrbitPeriod K a) :=
  four_dvd_totalTurnZ_of_iterate_eq K a.1 (dartOrbitPeriod K a) (orbit_iterate_period_eq K a)

/-- The total signed turning around a boundary orbit is at most the orbit length in absolute
  value. -/
theorem abs_orbit_totalTurnZ_le (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ (dartOrbitPeriod K a : ℤ) :=
  abs_totalTurnZ_le K a.1 (dartOrbitPeriod K a)

/-- The boundary orbit through `a` turns by exactly one full revolution, i.e. its total signed
  turning is `4` or `-4` quarter turns. -/
def TurningIsFullRevolution (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    Prop :=
  totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
    totalTurnZ K a.1 (dartOrbitPeriod K a) = -4

/-- A boundary orbit that makes a full revolution has length at least `4`. -/
theorem orbitPeriod_ge_four_of_fullRevolution (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : TurningIsFullRevolution K a) :
    4 ≤ dartOrbitPeriod K a := by
  have hbound := abs_orbit_totalTurnZ_le K a
  have h4 : (4 : ℤ) ≤ |totalTurnZ K a.1 (dartOrbitPeriod K a)| := by
    rcases h with h | h <;> rw [h] <;> decide
  have : (4 : ℤ) ≤ (dartOrbitPeriod K a : ℤ) := le_trans h4 hbound
  exact_mod_cast this

end Lattice

end StatMech
