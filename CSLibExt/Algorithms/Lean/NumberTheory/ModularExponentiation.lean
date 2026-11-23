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

/-- **Modular exponentiation.** For natural numbers $a$, $b$ and $n$, modular exponentiation with
base $a$, exponent $b$ and modulus $n$ is the recursive procedure that returns $1$ if $b = 0$. If
$b > 0$ is even, it computes the result $d$ for exponent $b/2$ (same base and modulus) and returns
$d \cdot d \bmod n$. If $b$ is odd, it computes the result $d$ for exponent $b - 1$ and returns
$a \cdot d \bmod n$. Each even or odd step performs one multiplication, and the cost of the
procedure is the total number of multiplications performed.

Source: CLRS4 §31.6, printed page 934, `MODULAR-EXPONENTIATION`, with one tick per
multiplication. -/
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

/-- **Base case of modular exponentiation.** For all natural numbers $a$ and $n$, modular
exponentiation with base $a$, exponent $0$ and modulus $n$ returns $1$ and performs no
multiplications. -/
@[simp]
theorem modularExponentiation_zero (a n : Nat) :
    modularExponentiation a 0 n = ⟨1, 0⟩ := by
  rw [modularExponentiation]
  rfl

/-- **Even step of modular exponentiation.** Let $a$, $b$, $n$ be natural numbers with $b > 0$
and $b$ even. If modular exponentiation on base $a$, exponent $b/2$ and modulus $n$ returns the
value $d$ using $t$ multiplications, then on base $a$, exponent $b$ and modulus $n$ it returns
the value $(d \cdot d) \bmod n$ using $t + 1$ multiplications. -/
theorem modularExponentiation_even (a b n : Nat) (hb : 0 < b) (heven : b % 2 = 0) :
    modularExponentiation a b n =
      let d := modularExponentiation a (b / 2) n
      ⟨(d.ret * d.ret) % n, d.time + 1⟩ := by
  rw [modularExponentiation]
  simp only [dite_eq_right (Nat.ne_of_gt hb), dite_eq_left heven]
  rfl

/-- **Odd step of modular exponentiation.** Let $a$, $b$, $n$ be natural numbers with $b$ odd.
If modular exponentiation on base $a$, exponent $b - 1$ and modulus $n$ returns the value $d$
using $t$ multiplications, then on base $a$, exponent $b$ and modulus $n$ it returns the value
$(a \cdot d) \bmod n$ using $t + 1$ multiplications. -/
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

/-- **Modular exponentiation returns 1 at exponent zero.** For all natural numbers $a$ and $n$,
modular exponentiation with base $a$, exponent $0$ and modulus $n$ returns $1$.

In particular the returned value is $1$ even when $n = 1$, so it is not reduced modulo $n$. -/
@[simp]
theorem modularExponentiation_ret_zero (a n : Nat) :
    (modularExponentiation a 0 n).ret = 1 := by
  rw [modularExponentiation_zero]

/-- **No multiplications at exponent zero.** For all natural numbers $a$ and $n$, modular
exponentiation with base $a$, exponent $0$ and modulus $n$ performs no multiplications. -/
@[simp]
theorem modularExponentiation_time_zero (a n : Nat) :
    (modularExponentiation a 0 n).time = 0 := by
  rw [modularExponentiation_zero]

/-- **Value of the even step of modular exponentiation.** Let $a$, $b$, $n$ be natural numbers
with $b > 0$ and $b$ even, and let $d$ be the value returned by modular exponentiation on base
$a$, exponent $b/2$ and modulus $n$. Then the value returned on base $a$, exponent $b$ and
modulus $n$ is $(d \cdot d) \bmod n$. -/
theorem modularExponentiation_ret_even (a b n : Nat) (hb : 0 < b)
    (heven : b % 2 = 0) :
    (modularExponentiation a b n).ret =
      let d := (modularExponentiation a (b / 2) n).ret
      (d * d) % n := by
  rw [modularExponentiation_even a b n hb heven]

/-- **Multiplication count in the even case.** Let $a$, $b$ and $n$ be natural numbers with $b$
positive and even. Modular exponentiation with base $a$, exponent $b$ and modulus $n$ performs
exactly one more multiplication than it does with base $a$, exponent $b/2$ and modulus $n$. -/
theorem modularExponentiation_time_even (a b n : Nat) (hb : 0 < b)
    (heven : b % 2 = 0) :
    (modularExponentiation a b n).time =
      (modularExponentiation a (b / 2) n).time + 1 := by
  rw [modularExponentiation_even a b n hb heven]

/-- **Value of the odd step of modular exponentiation.** Let $a$, $b$, $n$ be natural numbers
with $b$ odd, and let $d$ be the value returned by modular exponentiation on base $a$, exponent
$b - 1$ and modulus $n$. Then the value returned on base $a$, exponent $b$ and modulus $n$ is
$(a \cdot d) \bmod n$. -/
theorem modularExponentiation_ret_odd (a b n : Nat) (hodd : b % 2 ≠ 0) :
    (modularExponentiation a b n).ret =
      (a * (modularExponentiation a (b - 1) n).ret) % n := by
  rw [modularExponentiation_odd a b n hodd]

/-- **Multiplication count in the odd case.** Let $a$, $b$ and $n$ be natural numbers with $b$ odd.
Modular exponentiation with base $a$, exponent $b$ and modulus $n$ performs exactly one more
multiplication than it does with base $a$, exponent $b - 1$ and modulus $n$. -/
theorem modularExponentiation_time_odd (a b n : Nat) (hodd : b % 2 ≠ 0) :
    (modularExponentiation a b n).time =
      (modularExponentiation a (b - 1) n).time + 1 := by
  rw [modularExponentiation_odd a b n hodd]

/-- **Modular exponentiation is correct up to reduction.** For natural numbers $a$, $b$, $n$
with $n > 0$, including $b = 0$, the value $r$ returned by modular exponentiation on base $a$,
exponent $b$ and modulus $n$ satisfies $r \bmod n = a^b \bmod n$. -/
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

/-- **Modular exponentiation with a reduced base.** For natural numbers $a$, $b$, $n$ with
$n > 0$, the value $r$ returned by modular exponentiation on base $a$, exponent $b$ and
modulus $n$ satisfies $r \bmod n = (a \bmod n)^b \bmod n$. -/
theorem modularExponentiation_ret_mod_base (a b n : Nat) (hn : 0 < n) :
    (modularExponentiation a b n).ret % n = (a % n) ^ b % n := by
  calc
    (modularExponentiation a b n).ret % n = a ^ b % n :=
      modularExponentiation_ret_mod a b n hn
    _ = (a % n) ^ b % n := Nat.pow_mod a b n

/-- **Modular exponentiation returns a reduced value.** For natural numbers $a$, $b$, $n$ with
$b > 0$, the value $r$ returned by modular exponentiation on base $a$, exponent $b$ and
modulus $n$ satisfies $r \bmod n = r$ (with the convention $r \bmod 0 = r$). -/
theorem modularExponentiation_ret_is_reduced (a b n : Nat) (hb : 0 < b) :
    (modularExponentiation a b n).ret % n =
      (modularExponentiation a b n).ret := by
  by_cases heven : b % 2 = 0
  · rw [modularExponentiation_ret_even a b n hb heven]
    exact Nat.mod_mod _ _
  · rw [modularExponentiation_ret_odd a b n heven]
    exact Nat.mod_mod _ _

/-- **Correctness of modular exponentiation.** For natural numbers $a$, $b$, $n$ with $b > 0$
and $n > 0$, the value returned by modular exponentiation on base $a$, exponent $b$ and
modulus $n$ equals $a^b \bmod n$. -/
theorem modularExponentiation_correct (a b n : Nat) (hb : 0 < b) (hn : 0 < n) :
    (modularExponentiation a b n).ret = a ^ b % n := by
  calc
    (modularExponentiation a b n).ret =
        (modularExponentiation a b n).ret % n :=
      (modularExponentiation_ret_is_reduced a b n hb).symm
    _ = a ^ b % n := modularExponentiation_ret_mod a b n hn

/-- **Modular exponentiation returns a value below the modulus.** For natural numbers $a$, $b$,
$n$ with $b > 0$ and $n > 0$, the value returned by modular exponentiation on base $a$,
exponent $b$ and modulus $n$ is less than $n$. -/
theorem modularExponentiation_lt (a b n : Nat) (hb : 0 < b) (hn : 0 < n) :
    (modularExponentiation a b n).ret < n := by
  rw [modularExponentiation_correct a b n hb hn]
  exact Nat.mod_lt _ hn

/-- **Modular exponentiation returns the least residue.** For natural numbers $a$, $b$, $n$ with
$b > 0$ and $n > 0$, the value $r$ returned by modular exponentiation on base $a$, exponent $b$
and modulus $n$ satisfies $r = a^b \bmod n$ and $r < n$. -/
theorem modularExponentiation_is_leastResidue (a b n : Nat) (hb : 0 < b) (hn : 0 < n) :
    (modularExponentiation a b n).ret = a ^ b % n ∧
      (modularExponentiation a b n).ret < n :=
  ⟨modularExponentiation_correct a b n hb hn,
    modularExponentiation_lt a b n hb hn⟩

/-- **Least residue at exponent zero.** For all natural numbers $a$ and $n$ with $n > 1$, the value
returned by modular exponentiation with base $a$, exponent $0$ and modulus $n$ equals $a^0 \bmod n$
and is less than $n$. -/
theorem modularExponentiation_zero_is_leastResidue (a n : Nat) (hn : 1 < n) :
    (modularExponentiation a 0 n).ret = a ^ 0 % n ∧
      (modularExponentiation a 0 n).ret < n := by
  rw [modularExponentiation_ret_zero]
  simp only [Nat.pow_zero]
  rw [Nat.mod_eq_of_lt hn]
  exact ⟨rfl, hn⟩

/-- **Unreduced result at modulus one.** For every natural number $a$, modular exponentiation with
base $a$, exponent $0$ and modulus $1$ returns $1$, whereas $a^0 \bmod 1 = 0$.

The base case of the CLRS procedure returns $1$ without reducing it modulo the modulus; this
boundary case keeps that visible. -/
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

/-- **The multiplication count depends only on the exponent.** For all natural numbers $a$, $a'$,
$b$, $n$ and $n'$, modular exponentiation performs the same number of multiplications with base
$a$, exponent $b$ and modulus $n$ as with base $a'$, exponent $b$ and modulus $n'$. -/
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

/-- **Multiplication count of modular exponentiation.** Let $a$, $b$ and $n$ be natural numbers
with $b > 0$, and let $\beta = \lfloor \log_2 b \rfloor + 1$ be the number of binary digits of $b$.
The number of multiplications performed by modular exponentiation with base $a$, exponent $b$ and
modulus $n$ is at least $\beta$ and at most $2\beta - 1$. -/
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
