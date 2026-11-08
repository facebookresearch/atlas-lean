/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Log
public import Cslib.Algorithms.Lean.TimeM

import Mathlib.Tactic.Ring
import Mathlib.Data.List.Nodup

/-!
# Modular linear equations

The solver follows the ordered enumeration in CLRS, using the coefficient produced by the
canonical extended Euclidean accumulator with the operands reversed.
Printing is represented by an ordered array of least nonnegative residues.

The source is CLRS, fourth edition, Section 31.4, printed pages 925-927,
with EXTENDED-EUCLID from Section 31.2, printed pages 914-915.

Its cost counts six arithmetic operations per nonterminal extended-Euclid transition, one
divisibility remainder, four successful-branch setup operations, and three operations per output.
This is an arithmetic-event model, not a bit, word-RAM, allocation, stack, or output-space model.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.ModularLinearEquation

open Cslib.Algorithms.Lean

set_option autoImplicit false

@[no_expose] private def countedXgcdAux
    (r : Nat) (s t : Int) (r' : Nat) (s' t' : Int) : TimeM Nat (Nat × Int × Int) :=
  if h : r = 0 then
    ⟨(r', s', t'), 0⟩
  else
    let q : Int := r' / r
    let next := countedXgcdAux (r' % r) (s' - q * s) (t' - q * t) r s t
    ⟨next.ret, next.time + 6⟩
termination_by r
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

private theorem countedXgcdAux_ret
    (r : Nat) (s t : Int) (r' : Nat) (s' t' : Int) :
    (countedXgcdAux r s t r' s' t').ret = Nat.xgcdAux r s t r' s' t' := by
  induction r using Nat.strongRecOn generalizing s t r' s' t' with
  | ind r ih =>
    by_cases hr : r = 0
    · subst r
      simp [countedXgcdAux]
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      rw [countedXgcdAux, dite_eq_right hr]
      dsimp only
      rw [ih (r' % r) (Nat.mod_lt _ hrpos)]
      exact (Nat.xgcdAux_rec hrpos).symm

private def xgcdSteps (r r' : Nat) : Nat :=
  if h : r = 0 then 0 else xgcdSteps (r' % r) r + 1
termination_by r
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

private theorem countedXgcdAux_time
    (r : Nat) (s t : Int) (r' : Nat) (s' t' : Int) :
    (countedXgcdAux r s t r' s' t').time = 6 * xgcdSteps r r' := by
  induction r using Nat.strongRecOn generalizing s t r' s' t' with
  | ind r ih =>
    by_cases hr : r = 0
    · subst r
      simp [countedXgcdAux, xgcdSteps]
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      rw [countedXgcdAux, dite_eq_right hr, xgcdSteps, dite_eq_right hr]
      dsimp only
      rw [ih (r' % r) (Nat.mod_lt _ hrpos)]
      omega

private theorem secondRemainder_le_half (r r' : Nat) (hr : 0 < r)
    (hu : r' % r ≠ 0) :
    r % (r' % r) ≤ r / 2 := by
  let u := r' % r
  have hu' : u ≠ 0 := by simpa [u] using hu
  have hupos : 0 < u := Nat.pos_of_ne_zero hu'
  have hult : u < r := Nat.mod_lt _ hr
  by_cases hhalf : u ≤ r / 2
  · exact (Nat.mod_lt r hupos).le.trans hhalf
  · have htwou : r < 2 * u := by omega
    have hru : r % u = r - u := by
      rw [Nat.mod_eq_sub_mod hult.le]
      exact Nat.mod_eq_of_lt (by omega)
    change r % u ≤ r / 2
    rw [hru]
    omega

private theorem xgcdSteps_le (r r' : Nat) : xgcdSteps r r' ≤ 2 * Nat.log2 r + 2 := by
  induction r using Nat.strongRecOn generalizing r' with
  | ind r ih =>
    by_cases hr : r = 0
    · subst r
      simp [xgcdSteps]
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      let u := r' % r
      have hult : u < r := Nat.mod_lt _ hrpos
      rw [xgcdSteps, dite_eq_right hr]
      change xgcdSteps u r + 1 ≤ 2 * Nat.log2 r + 2
      by_cases hu : u = 0
      · rw [xgcdSteps, dite_eq_left hu]
        omega
      · have hupos : 0 < u := Nat.pos_of_ne_zero hu
        have hr2 : 2 ≤ r := by omega
        rw [xgcdSteps, dite_eq_right hu]
        have hvle : r % u ≤ r / 2 := secondRemainder_le_half r r' hrpos (by simpa [u])
        have hvlt : r % u < r := (Nat.mod_lt r hupos).trans hult
        have hsteps := ih (r % u) hvlt u
        have hlog : Nat.log2 (r % u) ≤ Nat.log2 (r / 2) := by
          simpa only [Nat.log2_eq_log_two] using (Nat.log_mono_right (b := 2) hvle)
        rw [Nat.log2_def r, ite_eq_left hr2]
        omega

/-- Solves `a * x ≡ b [ZMOD n]`, returning the least residues in CLRS source order. -/
@[no_expose]
def modularLinearEquationSolver
    (a : Nat) (b : Int) (n : Nat) (_ha : 0 < a) (_hn : 0 < n) :
    TimeM Nat (Array Nat) :=
  let extended := countedXgcdAux n 1 0 a 0 1
  let d := extended.ret.1
  if (d : Int) ∣ b then
    let seed := (extended.ret.2.2 * (b / (d : Int))) % (n : Int)
    let stride := n / d
    let values := (List.range d).map (fun (i : Nat) =>
      ((seed + (i : Int) * (stride : Int)) % (n : Int)).toNat)
    ⟨values.toArray, extended.time + 1 + 4 + 3 * d⟩
  else
    ⟨#[], extended.time + 1⟩

/-- The returned list is the CLRS progression built from the canonical extended-GCD coefficient. -/
theorem modularLinearEquationSolver_ret
    (a : Nat) (b : Int) (n : Nat) (ha : 0 < a) (hn : 0 < n) :
    (modularLinearEquationSolver a b n ha hn).ret.toList =
      if (Nat.gcd a n : Int) ∣ b then
        (List.range (Nat.gcd a n)).map (fun (i : Nat) =>
          (((Nat.gcdB n a * (b / (Nat.gcd a n : Int))) % (n : Int) +
            (i : Int) * ((n / Nat.gcd a n : Nat) : Int)) % (n : Int)).toNat)
      else [] := by
  unfold modularLinearEquationSolver
  simp only [countedXgcdAux_ret, Nat.xgcdAux_val, Nat.xgcd_val,
    Nat.gcd_comm n a]
  split <;> simp

private theorem gcd_dvd_of_modEq
    (a n x : Nat) (b : Int) (h : Int.ModEq (n : Int) ((a : Int) * (x : Int)) b) :
    (Nat.gcd a n : Int) ∣ b := by
  have hdn : (Nat.gcd a n : Int) ∣ (n : Int) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right a n)
  have hda : (Nat.gcd a n : Int) ∣ (a : Int) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left a n)
  have hdiff : (Nat.gcd a n : Int) ∣ b - (a : Int) * (x : Int) :=
    hdn.trans (Int.modEq_iff_dvd.mp h)
  have hax : (Nat.gcd a n : Int) ∣ (a : Int) * (x : Int) :=
    dvd_mul_of_dvd_left hda _
  convert Int.dvd_add hdiff hax using 1
  ring

private theorem seed_sound
    (a b n : Int) (d : Nat) (hd : (d : Int) ∣ b)
    (hbezout : (d : Int) = n * Nat.gcdA n.natAbs a.natAbs + a * Nat.gcdB n.natAbs a.natAbs) :
    Int.ModEq n (a * ((Nat.gcdB n.natAbs a.natAbs * (b / (d : Int))) % n)) b := by
  have hraw : Int.ModEq n
      (a * (Nat.gcdB n.natAbs a.natAbs * (b / (d : Int)))) b := by
    rw [Int.modEq_iff_dvd]
    refine ⟨Nat.gcdA n.natAbs a.natAbs * (b / (d : Int)), ?_⟩
    have hdiv : (d : Int) * (b / (d : Int)) = b := Int.mul_ediv_cancel' hd
    calc
      b - a * (Nat.gcdB n.natAbs a.natAbs * (b / (d : Int))) =
          (d : Int) * (b / (d : Int)) -
            a * (Nat.gcdB n.natAbs a.natAbs * (b / (d : Int))) := by rw [hdiv]
      _ = n * (Nat.gcdA n.natAbs a.natAbs * (b / (d : Int))) := by
        rw [hbezout]
        ring
  have hnorm :=
    (Int.mod_modEq (Nat.gcdB n.natAbs a.natAbs * (b / (d : Int))) n).mul_left a
  exact hnorm.trans hraw

private theorem sourceSeed_sound
    (a : Nat) (b : Int) (n : Nat) (hd : (Nat.gcd a n : Int) ∣ b) :
    Int.ModEq (n : Int)
      ((a : Int) * ((Nat.gcdB n a * (b / (Nat.gcd a n : Int))) % (n : Int))) b := by
  apply seed_sound (a := (a : Int)) (b := b) (n := (n : Int))
    (d := Nat.gcd a n) hd
  simpa [Nat.gcd_comm, Int.natAbs_natCast, add_comm] using Nat.gcd_eq_gcd_ab n a

private theorem progression_sound
    (a : Nat) (b : Int) (n : Nat) (hd : (Nat.gcd a n : Int) ∣ b) (i : Nat) :
    Int.ModEq (n : Int)
      ((a : Int) *
        (((Nat.gcdB n a * (b / (Nat.gcd a n : Int))) % (n : Int) +
          (i : Int) * ((n / Nat.gcd a n : Nat) : Int)) % (n : Int))) b := by
  let d := Nat.gcd a n
  let seed := (Nat.gcdB n a * (b / (d : Int))) % (n : Int)
  let stride := n / d
  have hda : d ∣ a := Nat.gcd_dvd_left a n
  have hdn : d ∣ n := Nat.gcd_dvd_right a n
  have hmultiple : (n : Int) ∣ (a : Int) * ((i : Int) * (stride : Int)) := by
    refine ⟨((a / d : Nat) : Int) * (i : Int), ?_⟩
    have haeq : (d : Int) * ((a / d : Nat) : Int) = (a : Int) := by
      exact_mod_cast Nat.mul_div_cancel' hda
    have hneq : (d : Int) * (stride : Int) = (n : Int) := by
      exact_mod_cast Nat.mul_div_cancel' hdn
    rw [← haeq, ← hneq]
    ring
  have hstep : Int.ModEq (n : Int) ((a : Int) * ((i : Int) * (stride : Int))) 0 :=
    Int.modEq_zero_iff_dvd.mpr hmultiple
  have hseed : Int.ModEq (n : Int) ((a : Int) * seed) b := by
    simpa [d, seed] using sourceSeed_sound a b n hd
  have hadd := hseed.add hstep
  have hnorm := (Int.mod_modEq (seed + (i : Int) * (stride : Int)) (n : Int)).mul_left (a : Int)
  exact hnorm.trans (by simpa [mul_add, d, seed, stride] using hadd)

private theorem progression_lt
    (a : Nat) (b : Int) (n : Nat) (hn : 0 < n) (i : Nat) :
    (((Nat.gcdB n a * (b / (Nat.gcd a n : Int))) % (n : Int) +
      (i : Int) * ((n / Nat.gcd a n : Nat) : Int)) % (n : Int)).toNat < n := by
  have hn' : (n : Int) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Int.toNat_lt (Int.emod_nonneg _ hn')]
  simpa using Int.emod_lt _ hn'

private theorem progression_complete
    (a : Nat) (b : Int) (n x : Nat) (hn : 0 < n)
    (hd : (Nat.gcd a n : Int) ∣ b) (hx : x < n)
    (hsol : Int.ModEq (n : Int) ((a : Int) * (x : Int)) b) :
    ∃ i < Nat.gcd a n,
      (((Nat.gcdB n a * (b / (Nat.gcd a n : Int))) % (n : Int) +
        (i : Int) * ((n / Nat.gcd a n : Nat) : Int)) % (n : Int)).toNat = x := by
  let d := Nat.gcd a n
  let seed := (Nat.gcdB n a * (b / (d : Int))) % (n : Int)
  let stride := n / d
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_right a hn
  have hdn : d ∣ n := Nat.gcd_dvd_right a n
  have hn' : (0 : Int) < (n : Int) := by exact_mod_cast hn
  have hseed : Int.ModEq (n : Int) ((a : Int) * seed) b := by
    simpa [d, seed] using sourceSeed_sound a b n hd
  have hcancel := Int.ModEq.cancel_left_div_gcd hn' (hsol.trans hseed.symm)
  have hstride : Int.ModEq (stride : Int) (x : Int) seed := by
    simpa [d, stride, Int.gcd_def, Int.natAbs_natCast, Nat.gcd_comm,
      Int.natCast_ediv] using hcancel
  obtain ⟨q, hq⟩ := Int.modEq_iff_add_fac.mp hstride
  let r := (-q) % (d : Int)
  let i := r.toNat
  have hd' : (d : Int) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hrnonneg : 0 ≤ r := Int.emod_nonneg _ hd'
  have hri : (i : Int) = r := Int.toNat_of_nonneg hrnonneg
  have hi : i < d := by
    rw [Int.toNat_lt hrnonneg]
    simpa [r] using Int.emod_lt _ hd'
  refine ⟨i, hi, ?_⟩
  have hrmod : Int.ModEq (d : Int) r (-q) := by
    simpa [r] using Int.mod_modEq (-q) (d : Int)
  have hsum : Int.ModEq (d : Int) (q + r) 0 := by
    simpa using hrmod.add_left q
  have hmul := Int.ModEq.mul_right' (c := (stride : Int)) hsum
  have hdn_eq : (d : Int) * (stride : Int) = (n : Int) := by
    exact_mod_cast Nat.mul_div_cancel' hdn
  have hmul' : Int.ModEq (n : Int) ((q + r) * (stride : Int)) 0 := by
    simpa [hdn_eq] using hmul
  have hsource : Int.ModEq (n : Int) (seed + r * (stride : Int)) (x : Int) := by
    have hadd := (Int.ModEq.refl (x : Int)).add hmul'
    rw [hq]
    simpa only [add_zero] using (show
      Int.ModEq (n : Int)
        ((x : Int) + (stride : Int) * q + r * (stride : Int))
        ((x : Int) + 0) by
          convert hadd using 1
          ring)
  have hsource_i : Int.ModEq (n : Int) (seed + (i : Int) * (stride : Int)) (x : Int) := by
    simpa [hri] using hsource
  have hx0 : (0 : Int) ≤ (x : Int) := Int.natCast_nonneg x
  have hxn : (x : Int) < (n : Int) := by exact_mod_cast hx
  have hxmod : (x : Int) % (n : Int) = (x : Int) := Int.emod_eq_of_lt hx0 hxn
  have hres : (seed + (i : Int) * (stride : Int)) % (n : Int) = (x : Int) :=
    hsource_i.eq.trans hxmod
  rw [← Int.toNat_natCast x]
  exact congrArg Int.toNat (by simpa [d, seed, stride] using hres)

private theorem progression_injective
    (a : Nat) (b : Int) (n : Nat) (hn : 0 < n) {i j : Nat}
    (hi : i < Nat.gcd a n) (hj : j < Nat.gcd a n)
    (hij :
      (((Nat.gcdB n a * (b / (Nat.gcd a n : Int))) % (n : Int) +
        (i : Int) * ((n / Nat.gcd a n : Nat) : Int)) % (n : Int)).toNat =
      (((Nat.gcdB n a * (b / (Nat.gcd a n : Int))) % (n : Int) +
        (j : Int) * ((n / Nat.gcd a n : Nat) : Int)) % (n : Int)).toNat) :
    i = j := by
  let d := Nat.gcd a n
  let seed := (Nat.gcdB n a * (b / (d : Int))) % (n : Int)
  let stride := n / d
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_right a hn
  have hdn : d ∣ n := Nat.gcd_dvd_right a n
  have hstridepos : 0 < stride := Nat.div_pos (Nat.le_of_dvd hn hdn) hdpos
  have hn' : (n : Int) ≠ 0 := by exact_mod_cast hn.ne'
  have hzi : 0 ≤ (seed + (i : Int) * (stride : Int)) % (n : Int) :=
    Int.emod_nonneg _ hn'
  have hzj : 0 ≤ (seed + (j : Int) * (stride : Int)) % (n : Int) :=
    Int.emod_nonneg _ hn'
  have hres :
      (seed + (i : Int) * (stride : Int)) % (n : Int) =
      (seed + (j : Int) * (stride : Int)) % (n : Int) := by
    have hcast := congrArg (fun k : Nat => (k : Int)) hij
    rw [Int.toNat_of_nonneg hzi, Int.toNat_of_nonneg hzj] at hcast
    simpa [d, seed, stride] using hcast
  have hmodeq : Int.ModEq (n : Int)
      (seed + (i : Int) * (stride : Int))
      (seed + (j : Int) * (stride : Int)) := hres
  have hprod : Int.ModEq (n : Int)
      ((i : Int) * (stride : Int)) ((j : Int) * (stride : Int)) :=
    Int.ModEq.add_left_cancel' seed hmodeq
  have hdn_eq : (d : Int) * (stride : Int) = (n : Int) := by
    exact_mod_cast Nat.mul_div_cancel' hdn
  have hprod' : Int.ModEq ((d : Int) * (stride : Int))
      ((i : Int) * (stride : Int)) ((j : Int) * (stride : Int)) := by
    simpa [hdn_eq] using hprod
  have hdmodeq : Int.ModEq (d : Int) (i : Int) (j : Int) :=
    Int.ModEq.mul_right_cancel' (by exact_mod_cast hstridepos.ne') hprod'
  have hi0 : (0 : Int) ≤ (i : Int) := Int.natCast_nonneg i
  have hj0 : (0 : Int) ≤ (j : Int) := Int.natCast_nonneg j
  have hid : (i : Int) < (d : Int) := by exact_mod_cast hi
  have hjd : (j : Int) < (d : Int) := by exact_mod_cast hj
  have hi_mod : (i : Int) % (d : Int) = (i : Int) := Int.emod_eq_of_lt hi0 hid
  have hj_mod : (j : Int) % (d : Int) = (j : Int) := Int.emod_eq_of_lt hj0 hjd
  have hij' : (i : Int) = (j : Int) := hi_mod.symm.trans (hdmodeq.eq.trans hj_mod)
  exact Int.ofNat_inj.mp hij'

/-- Membership characterizes exactly the least nonnegative solutions of the congruence. -/
theorem modularLinearEquationSolver_mem_iff
    (a : Nat) (b : Int) (n : Nat) (ha : 0 < a) (hn : 0 < n) (x : Nat) :
    x ∈ (modularLinearEquationSolver a b n ha hn).ret.toList ↔
      x < n ∧ Int.ModEq (n : Int) ((a : Int) * (x : Int)) b := by
  rw [modularLinearEquationSolver_ret]
  constructor
  · intro hx
    split at hx
    next hd =>
      simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨progression_lt a b n hn i, ?_⟩
      have hn' : (n : Int) ≠ 0 := by exact_mod_cast hn.ne'
      have hnonneg := Int.emod_nonneg
        ((Nat.gcdB n a * (b / (Nat.gcd a n : Int))) % (n : Int) +
          (i : Int) * ((n / Nat.gcd a n : Nat) : Int)) hn'
      rw [Int.toNat_of_nonneg hnonneg]
      exact progression_sound a b n hd i
    next hd => simp at hx
  · rintro ⟨hx, hsol⟩
    have hd := gcd_dvd_of_modEq a n x b hsol
    rw [ite_eq_left hd]
    simp only [List.mem_map, List.mem_range]
    obtain ⟨i, hi, hix⟩ := progression_complete a b n x hn hd hx hsol
    exact ⟨i, hi, hix⟩

/-- The ordered result contains no repeated residues. -/
theorem modularLinearEquationSolver_nodup
    (a : Nat) (b : Int) (n : Nat) (ha : 0 < a) (hn : 0 < n) :
    (modularLinearEquationSolver a b n ha hn).ret.toList.Nodup := by
  rw [modularLinearEquationSolver_ret]
  split
  next _ =>
    apply List.Nodup.map_on
    · intro i hi j hj hij
      exact progression_injective a b n hn
        (List.mem_range.mp hi) (List.mem_range.mp hj) hij
    · exact List.nodup_range
  next _ => simp

/-- The solver returns `gcd a n` residues exactly when the congruence is solvable. -/
theorem modularLinearEquationSolver_length
    (a : Nat) (b : Int) (n : Nat) (ha : 0 < a) (hn : 0 < n) :
    (modularLinearEquationSolver a b n ha hn).ret.size =
      if (Nat.gcd a n : Int) ∣ b then Nat.gcd a n else 0 := by
  have h := congrArg List.length (modularLinearEquationSolver_ret a b n ha hn)
  split at h <;> simp_all

/-- The returned array is empty exactly when `gcd a n` does not divide `b`. -/
theorem modularLinearEquationSolver_empty_iff
    (a : Nat) (b : Int) (n : Nat) (ha : 0 < a) (hn : 0 < n) :
    (modularLinearEquationSolver a b n ha hn).ret = #[] ↔
      ¬ ((Nat.gcd a n : Int) ∣ b) := by
  constructor
  · intro hempty hdvd
    have hsize := modularLinearEquationSolver_length a b n ha hn
    rw [ite_eq_left hdvd, hempty] at hsize
    simp at hsize
    exact (Nat.gcd_pos_of_pos_right a hn).ne' hsize.symm
  · intro hdvd
    have h := modularLinearEquationSolver_ret a b n ha hn
    simp [hdvd] at h
    simpa using h

/-- The selected arithmetic-event cost is bounded by the source logarithmic-plus-output bound. -/
theorem modularLinearEquationSolver_time_bounds
    (a : Nat) (b : Int) (n : Nat) (ha : 0 < a) (hn : 0 < n) :
    1 + (if (Nat.gcd a n : Int) ∣ b then 4 + 3 * Nat.gcd a n else 0)
      ≤ (modularLinearEquationSolver a b n ha hn).time ∧
    (modularLinearEquationSolver a b n ha hn).time
      ≤ 6 * (2 * Nat.log2 n + 2) + 1 +
        (if (Nat.gcd a n : Int) ∣ b then 4 + 3 * Nat.gcd a n else 0) := by
  unfold modularLinearEquationSolver
  simp only [countedXgcdAux_ret, Nat.xgcdAux_val, Nat.xgcd_val, Nat.gcd_comm n a,
    countedXgcdAux_time]
  have hsteps := xgcdSteps_le n a
  split <;> dsimp only <;> omega

end Cslib.Algorithms.Lean.ModularLinearEquation
