/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Init.Data.Nat.Lemmas
public import Init.Data.Nat.Log2

import Lean.Elab.Tactic.Omega

/-!
# Recursive modular exponentiation

Source: CLRS, fourth edition, §31.6, printed page 934,
`MODULAR-EXPONENTIATION`; the bit-length analysis is on printed page 935.

The cost model charges one unit for each multiplication executed by the
CLRS4 parity recursion. Branch tests, natural-number arithmetic, remainder,
and recursive-call dispatch are free.

The source algorithm literally returns `1` at exponent zero. Consequently,
its raw result is not normalized when the modulus is one; reducing the result
recovers the usual modular-power specification in that case.
-/

set_option autoImplicit false

@[expose] public section

namespace Cslib.Algorithms.Lean.ModularExponentiation

open Cslib.Algorithms.Lean

/-- CLRS4 §31.6, printed page 934, `MODULAR-EXPONENTIATION`, with one tick per multiplication. -/
def modularExponentiation (a b n : Nat) : TimeM Nat Nat :=
  if _hzero : b = 0 then
    pure 1
  else if _heven : b % 2 = 0 then
    do
      let d ← modularExponentiation a (b / 2) n
      TimeM.tick 1
      pure ((d * d) % n)
  else
    do
      let d ← modularExponentiation a (b - 1) n
      TimeM.tick 1
      pure ((a * d) % n)
termination_by b
decreasing_by
  · exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero _hzero) (by decide)
  · exact Nat.sub_lt (Nat.zero_lt_of_ne_zero _hzero) (by decide)

/-- The source base clause returns literal `1` and performs no multiplication. -/
@[simp]
theorem modularExponentiation_zero (a n : Nat) :
    modularExponentiation a 0 n = ⟨1, 0⟩ := by
  rw [modularExponentiation]
  rfl

/-- The positive even branch squares the result of the source `b / 2` recursion. -/
theorem modularExponentiation_even (a b n : Nat) (hb : 0 < b) (heven : b % 2 = 0) :
    modularExponentiation a b n =
      let d := modularExponentiation a (b / 2) n
      ⟨(d.ret * d.ret) % n, d.time + 1⟩ := by
  rw [modularExponentiation]
  simp only [dite_eq_right (Nat.ne_of_gt hb), dite_eq_left heven]
  rfl

/-- The odd branch first recurses at `b - 1`, then multiplies by the original base. -/
theorem modularExponentiation_odd (a b n : Nat) (hodd : b % 2 ≠ 0) :
    modularExponentiation a b n =
      let d := modularExponentiation a (b - 1) n
      ⟨(a * d.ret) % n, d.time + 1⟩ := by
  have hzero : b ≠ 0 := by
    intro hb
    subst b
    exact hodd rfl
  rw [modularExponentiation]
  simp only [dite_eq_right hzero, dite_eq_right hodd]
  rfl

/-- The raw zero-exponent result is literal `1`, even when the modulus is one. -/
@[simp]
theorem modularExponentiation_ret_zero (a n : Nat) :
    (modularExponentiation a 0 n).ret = 1 := by
  rw [modularExponentiation_zero]

/-- Exponent zero performs no multiplication. -/
@[simp]
theorem modularExponentiation_time_zero (a n : Nat) :
    (modularExponentiation a 0 n).time = 0 := by
  rw [modularExponentiation_zero]

/-- Raw-result projection of the source positive even branch. -/
theorem modularExponentiation_ret_even (a b n : Nat) (hb : 0 < b)
    (heven : b % 2 = 0) :
    (modularExponentiation a b n).ret =
      let d := (modularExponentiation a (b / 2) n).ret
      (d * d) % n := by
  rw [modularExponentiation_even a b n hb heven]

/-- The even source branch adds exactly one multiplication to its child cost. -/
theorem modularExponentiation_time_even (a b n : Nat) (hb : 0 < b)
    (heven : b % 2 = 0) :
    (modularExponentiation a b n).time =
      (modularExponentiation a (b / 2) n).time + 1 := by
  rw [modularExponentiation_even a b n hb heven]

/-- Raw-result projection of the source odd branch, with the original base first. -/
theorem modularExponentiation_ret_odd (a b n : Nat) (hodd : b % 2 ≠ 0) :
    (modularExponentiation a b n).ret =
      (a * (modularExponentiation a (b - 1) n).ret) % n := by
  rw [modularExponentiation_odd a b n hodd]

/-- The odd source branch adds exactly one multiplication after its `b - 1` child. -/
theorem modularExponentiation_time_odd (a b n : Nat) (hodd : b % 2 ≠ 0) :
    (modularExponentiation a b n).time =
      (modularExponentiation a (b - 1) n).time + 1 := by
  rw [modularExponentiation_odd a b n hodd]

/-- Reducing the raw result gives the canonical modular power, including at exponent zero. -/
theorem modularExponentiation_ret_mod (a b n : Nat) (_hn : 0 < n) :
    (modularExponentiation a b n).ret % n = a ^ b % n := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
      by_cases hzero : b = 0
      · subst b
        simp
      · have hb : 0 < b := Nat.zero_lt_of_ne_zero hzero
        by_cases heven : b % 2 = 0
        · have hhalf : b / 2 < b := Nat.div_lt_self hb (by decide)
          have hdecomp : (b / 2) * 2 = b := by
            have h := Nat.div_add_mod b 2
            omega
          have hpow : a ^ (b / 2) * a ^ (b / 2) = a ^ b := by
            calc
              a ^ (b / 2) * a ^ (b / 2) = (a ^ (b / 2)) ^ 2 :=
                (Nat.pow_two _).symm
              _ = a ^ ((b / 2) * 2) := (Nat.pow_mul a (b / 2) 2).symm
              _ = a ^ b := by rw [hdecomp]
          rw [modularExponentiation_ret_even a b n hb heven]
          rw [Nat.mod_mod, Nat.mul_mod, ih (b / 2) hhalf]
          rw [← Nat.mul_mod, hpow]
        · have hsub : b - 1 < b := Nat.sub_lt hb (by decide)
          have hdecomp : 1 + (b - 1) = b := by omega
          have hpow : a * a ^ (b - 1) = a ^ b := by
            calc
              a * a ^ (b - 1) = a ^ 1 * a ^ (b - 1) := by simp
              _ = a ^ (1 + (b - 1)) := (Nat.pow_add a 1 (b - 1)).symm
              _ = a ^ b := by rw [hdecomp]
          rw [modularExponentiation_ret_odd a b n heven]
          rw [Nat.mod_mod, Nat.mul_mod, ih (b - 1) hsub]
          rw [← Nat.mul_mod, hpow]

/-- The same invariant with the base reduced before exponentiation. -/
theorem modularExponentiation_ret_mod_base (a b n : Nat) (hn : 0 < n) :
    (modularExponentiation a b n).ret % n = (a % n) ^ b % n := by
  calc
    (modularExponentiation a b n).ret % n = a ^ b % n :=
      modularExponentiation_ret_mod a b n hn
    _ = (a % n) ^ b % n := Nat.pow_mod a b n

/-- Every positive-exponent result has already been reduced modulo `n`. -/
theorem modularExponentiation_ret_is_reduced (a b n : Nat) (hb : 0 < b) :
    (modularExponentiation a b n).ret % n =
      (modularExponentiation a b n).ret := by
  by_cases heven : b % 2 = 0
  · rw [modularExponentiation_ret_even a b n hb heven]
    exact Nat.mod_mod _ _
  · rw [modularExponentiation_ret_odd a b n heven]
    exact Nat.mod_mod _ _

/-- For a positive exponent, the raw result is the least residue of `a ^ b`. -/
theorem modularExponentiation_correct (a b n : Nat) (hb : 0 < b) (hn : 0 < n) :
    (modularExponentiation a b n).ret = a ^ b % n := by
  calc
    (modularExponentiation a b n).ret =
        (modularExponentiation a b n).ret % n :=
      (modularExponentiation_ret_is_reduced a b n hb).symm
    _ = a ^ b % n := modularExponentiation_ret_mod a b n hn

/-- Positive-exponent results lie strictly below a positive modulus. -/
theorem modularExponentiation_lt (a b n : Nat) (hb : 0 < b) (hn : 0 < n) :
    (modularExponentiation a b n).ret < n := by
  rw [modularExponentiation_correct a b n hb hn]
  exact Nat.mod_lt _ hn

/-- The modular-power equality and least-residue range for positive exponents. -/
theorem modularExponentiation_is_leastResidue (a b n : Nat) (hb : 0 < b) (hn : 0 < n) :
    (modularExponentiation a b n).ret = a ^ b % n ∧
      (modularExponentiation a b n).ret < n :=
  ⟨modularExponentiation_correct a b n hb hn,
    modularExponentiation_lt a b n hb hn⟩

/-- With `n > 1`, the literal zero-exponent result is also the least residue. -/
theorem modularExponentiation_zero_is_leastResidue (a n : Nat) (hn : 1 < n) :
    (modularExponentiation a 0 n).ret = a ^ 0 % n ∧
      (modularExponentiation a 0 n).ret < n := by
  rw [modularExponentiation_ret_zero]
  simp only [Nat.pow_zero]
  rw [Nat.mod_eq_of_lt hn]
  exact ⟨rfl, hn⟩

/-- The CLRS base clause is deliberately visible at the modulus-one boundary. -/
theorem modularExponentiation_zero_modulus_one (a : Nat) :
    (modularExponentiation a 0 1).ret = 1 ∧ a ^ 0 % 1 = 0 := by
  simp

/-- Private count of child edges in the actual source exponent trace. -/
private def recursiveChildCalls (b : Nat) : Nat :=
  if hzero : b = 0 then
    0
  else if b % 2 = 0 then
    recursiveChildCalls (b / 2) + 1
  else
    recursiveChildCalls (b - 1) + 1
termination_by b
decreasing_by
  · exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero hzero) (by decide)
  · exact Nat.sub_lt (Nat.zero_lt_of_ne_zero hzero) (by decide)

@[simp]
private theorem recursiveChildCalls_zero : recursiveChildCalls 0 = 0 := by
  rw [recursiveChildCalls]
  rfl

private theorem recursiveChildCalls_even (b : Nat) (hb : 0 < b) (heven : b % 2 = 0) :
    recursiveChildCalls b = recursiveChildCalls (b / 2) + 1 := by
  rw [recursiveChildCalls]
  simp only [dite_eq_right (Nat.ne_of_gt hb), ite_eq_left heven]

private theorem recursiveChildCalls_odd (b : Nat) (hodd : b % 2 ≠ 0) :
    recursiveChildCalls b = recursiveChildCalls (b - 1) + 1 := by
  have hzero : b ≠ 0 := by
    intro hb
    subst b
    exact hodd rfl
  rw [recursiveChildCalls]
  simp only [dite_eq_right hzero, ite_eq_right hodd]

/-- The accumulated time is exactly the number of recursive child calls. -/
private theorem modularExponentiation_time_eq_recursiveChildCalls (a b n : Nat) :
    (modularExponentiation a b n).time = recursiveChildCalls b := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
      by_cases hzero : b = 0
      · subst b
        simp
      · have hb : 0 < b := Nat.zero_lt_of_ne_zero hzero
        by_cases heven : b % 2 = 0
        · have hhalf : b / 2 < b := Nat.div_lt_self hb (by decide)
          rw [modularExponentiation_time_even a b n hb heven]
          rw [recursiveChildCalls_even b hb heven, ih (b / 2) hhalf]
        · have hsub : b - 1 < b := Nat.sub_lt hb (by decide)
          rw [modularExponentiation_time_odd a b n heven]
          rw [recursiveChildCalls_odd b heven, ih (b - 1) hsub]

/-- Multiplication count depends on the exponent, not the base or modulus. -/
theorem modularExponentiation_time_independent (a a' b n n' : Nat) :
    (modularExponentiation a b n).time =
      (modularExponentiation a' b n').time := by
  rw [modularExponentiation_time_eq_recursiveChildCalls]
  rw [modularExponentiation_time_eq_recursiveChildCalls]

private theorem modularExponentiation_time_odd_pair (a b n : Nat) (hb : 1 < b)
    (hodd : b % 2 ≠ 0) :
    (modularExponentiation a b n).time =
      (modularExponentiation a (b / 2) n).time + 2 := by
  have hmodlt : b % 2 < 2 := Nat.mod_lt _ (by decide)
  have hmod : b % 2 = 1 := by omega
  have hdecomp : 2 * (b / 2) + b % 2 = b := Nat.div_add_mod b 2
  have hprev : b - 1 = 2 * (b / 2) := by omega
  have hprevPos : 0 < b - 1 := by omega
  have hprevEven : (b - 1) % 2 = 0 := by
    rw [hprev]
    omega
  have hprevHalf : (b - 1) / 2 = b / 2 := by
    rw [hprev]
    omega
  rw [modularExponentiation_time_odd a b n hodd]
  rw [modularExponentiation_time_even a (b - 1) n hprevPos hprevEven]
  rw [hprevHalf]

/-- For positive `b`, multiplication count lies between one and two per exponent bit. -/
theorem modularExponentiation_time_bounds (a b n : Nat) (hb : 0 < b) :
    let β := Nat.log2 b + 1
    β ≤ (modularExponentiation a b n).time ∧
      (modularExponentiation a b n).time ≤ 2 * β - 1 := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
      dsimp only
      by_cases hone : b = 1
      · subst b
        simp [Nat.log2_def, modularExponentiation]
      · have htwo : 2 ≤ b := by omega
        have hhalfPos : 0 < b / 2 := by omega
        have hhalf : b / 2 < b := Nat.div_lt_self hb (by decide)
        rcases ih (b / 2) hhalf hhalfPos with ⟨hlower, hupper⟩
        have hlog : Nat.log2 b = Nat.log2 (b / 2) + 1 := by
          rw [Nat.log2_def]
          simp [htwo]
        by_cases heven : b % 2 = 0
        · rw [modularExponentiation_time_even a b n hb heven]
          omega
        · have hpair := modularExponentiation_time_odd_pair a b n (by omega) heven
          rw [hpair]
          omega

end Cslib.Algorithms.Lean.ModularExponentiation
