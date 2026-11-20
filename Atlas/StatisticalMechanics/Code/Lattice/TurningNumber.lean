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

open SimpleGraph Function

namespace StatMech

namespace Lattice










theorem rot90Fun_iterate_four_eq (x : Site 2) : rot90Fun^[4] x = x := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  exact rot90Fun_four x


theorem rot90Fun_iterate_mod (n : ℕ) (x : Site 2) :
    rot90Fun^[n] x = rot90Fun^[n % 4] x := by
  conv_lhs => rw [← Nat.mod_add_div n 4]
  rw [Function.iterate_add_apply, Function.iterate_mul]
  congr 1
  exact Function.iterate_fixed (rot90Fun_iterate_four_eq x) (n / 4)




noncomputable def rotPow (s : ZMod 4) (x : Site 2) : Site 2 := rot90Fun^[s.val] x

@[simp] theorem rotPow_zero (x : Site 2) : rotPow 0 x = x := rfl

@[simp] theorem rotPow_one (x : Site 2) : rotPow 1 x = rot90Fun x := rfl


theorem rotPow_two (x : Site 2) : rotPow 2 x = -x := by
  show rot90Fun^[(2 : ZMod 4).val] x = -x
  have h : (2 : ZMod 4).val = 2 := by decide
  rw [h]; exact rot90Fun_rot90Fun x


theorem rotPow_three (x : Site 2) : rotPow 3 x = -rot90Fun x := by
  show rot90Fun^[(3 : ZMod 4).val] x = -rot90Fun x
  have h : (3 : ZMod 4).val = 3 := by decide
  rw [h]; show rot90Fun (rot90Fun (rot90Fun x)) = -rot90Fun x
  rw [rot90Fun_rot90Fun']




theorem rotPow_add (a b : ZMod 4) (x : Site 2) :
    rotPow (a + b) x = rotPow a (rotPow b x) := by
  unfold rotPow
  rw [← Function.iterate_add_apply, rot90Fun_iterate_mod (a.val + b.val),
    rot90Fun_iterate_mod (a + b).val, ZMod.val_add, Nat.mod_mod]









theorem neg_dartDir_ne_dartDir (e : Dart) : -e.dir ≠ e.dir := by
  intro h
  apply dartDir_ne_zero e
  funext i
  have hi := congrFun h i
  simp only [Pi.neg_apply, Pi.zero_apply] at hi ⊢
  omega


theorem zmod4_cases (s : ZMod 4) : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by decide +revert





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










noncomputable def turn (K : Set (Site 2)) (e : Dart) : ZMod 4 := by
  classical
  exact
    if e.head + (-rot90Fun e.dir) ∈ K then 1
    else if e.tail + (-rot90Fun e.dir) ∈ K then 0
    else 3



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














theorem dartNext_dir_eq_rotPow_turn (K : Set (Site 2)) (e : Dart) :
    (dartNext K e).dir = rotPow (turn K e) e.dir := by
  classical
  unfold turn
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [if_pos hA, (dartNext_front_head K e hA).2]; rfl
  · rw [if_neg hA]
    by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [if_pos hB, dartNext_straight_dir K e hA hB]; rfl
    · rw [if_neg hB, dartNext_left_dir K e hA hB, rotPow_three]










noncomputable def cumTurn (K : Set (Site 2)) (e : Dart) (k : ℕ) : ZMod 4 :=
  ∑ i ∈ Finset.range k, turn K ((dartNext K)^[i] e)

@[simp] theorem cumTurn_zero (K : Set (Site 2)) (e : Dart) : cumTurn K e 0 = 0 := by
  simp [cumTurn]



theorem cumTurn_succ (K : Set (Site 2)) (e : Dart) (k : ℕ) :
    cumTurn K e (k + 1) = turn K ((dartNext K)^[k] e) + cumTurn K e k := by
  unfold cumTurn; rw [Finset.sum_range_succ]; ring











theorem dir_iterate_eq_rotPow_cumTurn (K : Set (Site 2)) (e : Dart) (k : ℕ) :
    ((dartNext K)^[k] e).dir = rotPow (cumTurn K e k) e.dir := by
  induction k with
  | zero => rw [cumTurn_zero, rotPow_zero, Function.iterate_zero_apply]
  | succ n ih =>
    rw [Function.iterate_succ_apply', dartNext_dir_eq_rotPow_turn, ih, cumTurn_succ,
      rotPow_add]









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




theorem four_dvd_orbit_totalTurnZ (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (4 : ℤ) ∣ totalTurnZ K a.1 (dartOrbitPeriod K a) :=
  four_dvd_totalTurnZ_of_iterate_eq K a.1 (dartOrbitPeriod K a) (orbit_iterate_period_eq K a)




theorem abs_orbit_totalTurnZ_le (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ (dartOrbitPeriod K a : ℤ) :=
  abs_totalTurnZ_le K a.1 (dartOrbitPeriod K a)



















def TurningIsFullRevolution (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    Prop :=
  totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
    totalTurnZ K a.1 (dartOrbitPeriod K a) = -4








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
