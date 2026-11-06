/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Karatsuba multiplication

Karatsuba's algorithm multiplies two `n`-digit numbers with three recursive multiplications of
`⌈n/2⌉`-digit numbers instead of four. In base `B`, write `x = a * B^m + b` and `y = c * B^m + d`
with `m = ⌈n/2⌉` and `b, d < B^m`. Then

`x * y = B^(2m) * (a * c) + B^m * (a * d + b * c) + b * d`, and
`a * d + b * c = a * c + b * d - (a - b) * (c - d)`,

so the middle coefficient needs only the extra product `(a - b) * (c - d)`. This is the
subtraction form used by Erickson, *Algorithms* (2019), Section 1.9; Kleinberg–Tardos,
*Algorithm Design*, Section 5.5, present the equivalent addition form with third product
`(a + b) * (c + d)`. Working on natural numbers, `karatsuba` multiplies the magnitudes
`Nat.dist a b = |a - b|` and `Nat.dist c d` and adds or subtracts that product according to the
signs of `a - b` and `c - d`, so every recursive operand of an `n`-digit input has at most
`⌈n/2⌉` digits (`karatsuba_operands_lt`).

`karatsuba B n x y` returns `x * y` for all `B`, `n`, `x`, `y` (`karatsuba_ret`); the digit
count `n` only steers the recursion. Its cost depends only on `n`.

## Cost model

A call with `n ≤ 1` multiplies two digits and costs `1`. A call with `n ≥ 2` costs `n` for all
of its linear digit work (splitting, the two magnitude differences and their comparisons, the
additions and the shifts) plus its three recursive calls on `⌈n/2⌉` digits; recursion itself is
free. So the cost is `karatsubaCost n`, with `karatsubaCost n = 3 * karatsubaCost ⌈n/2⌉ + n`,
which is exactly `3^(k+1) - 2^(k+1) = 3 * n^(log₂ 3) - 2 * n` at `n = 2^k`, at most
`3^(⌈log₂ n⌉ + 1)` in general, and at most `9 * n^(log₂ 3)` for `n ≥ 1`. The model counts
base-`B` digit operations for inputs below `B^n`; it says nothing about machine words.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

/-- **Karatsuba multiplication.** Karatsuba's algorithm on natural numbers $x$ and $y$, viewed as
$n$-digit numbers in base $B$, as a computation that returns a natural number together with a
cost. If $n \le 1$, it returns $xy$ at cost $1$. If $n \ge 2$, let $m = \lceil n/2 \rceil$, let
$a$ and $b$ be the natural-number quotient and remainder of $x$ by $B^m$, and let $c$ and $d$ be
those of $y$ by $B^m$. It runs itself with digit count $m$ on the pairs $(a, c)$, $(b, d)$ and
$(|a - b|, |c - d|)$, with results $e$, $f$ and $g$, and returns $B^{2m} e + B^m h + f$, where
$h = e + f - g$ (subtraction truncated at $0$) if $b \le a$ holds exactly when $d \le c$, and
$h = e + f + g$ otherwise. The cost of the call is $n$ plus the costs of the three recursive
calls. -/
def karatsuba (B : ℕ) (n x y : ℕ) : TimeM ℕ ℕ :=
  if n ≤ 1 then do
    ✓
    pure (x * y)
  else do
    let m := (n + 1) / 2
    let a := x / B ^ m
    let b := x % B ^ m
    let c := y / B ^ m
    let d := y % B ^ m
    let e ← karatsuba B m a c
    let f ← karatsuba B m b d
    let g ← karatsuba B m (Nat.dist a b) (Nat.dist c d)
    ✓[n]
    let mid := if (b ≤ a ↔ d ≤ c) then e + f - g else e + f + g
    pure (B ^ (2 * m) * e + B ^ m * mid + f)
termination_by n
decreasing_by all_goals omega

/-- **Karatsuba cost recurrence.** The function $T$ on natural numbers defined by $T(n) = 1$ for
$n \le 1$ and $T(n) = 3\,T(\lceil n/2 \rceil) + n$ for $n \ge 2$.

It is the cost of Karatsuba multiplication on $n$ digits: one unit for a product of single
digits, and for $n \ge 2$ three recursive calls on $\lceil n/2 \rceil$ digits plus $n$ units of
linear digit work. -/
def karatsubaCost (n : ℕ) : ℕ :=
  if n ≤ 1 then 1 else 3 * karatsubaCost ((n + 1) / 2) + n
termination_by n
decreasing_by omega

/-! ## Correctness -/

/-- **Karatsuba's middle coefficient.** For all natural numbers $a, b, c, d$, write
$P = |a - b| \cdot |c - d|$. If $b \le a$ holds exactly when $d \le c$, then
$ac + bd - P = ad + bc$, where the subtraction is truncated at $0$; otherwise
$ac + bd + P = ad + bc$.

So the cross term $ad + bc$ is recovered from the three products $ac$, $bd$ and $P$. -/
theorem karatsuba_middle (a b c d : ℕ) :
    (if (b ≤ a ↔ d ≤ c) then a * c + b * d - Nat.dist a b * Nat.dist c d
      else a * c + b * d + Nat.dist a b * Nat.dist c d) = a * d + b * c := by
  by_cases hab : b ≤ a <;> by_cases hcd : d ≤ c
  · rw [Nat.dist_eq_sub_of_le_right hab, Nat.dist_eq_sub_of_le_right hcd]
    obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hab
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hcd
    simp only [ite_true, hab, hcd, Nat.add_sub_cancel_left]
    have : (b + p) * (d + q) + b * d - p * q + p * q = (b + p) * d + b * (d + q) + p * q := by
      rw [Nat.sub_add_cancel (by nlinarith)]
      ring
    omega
  · have hdc : c < d := Nat.lt_of_not_le hcd
    rw [Nat.dist_eq_sub_of_le_right hab, Nat.dist_eq_sub_of_le hdc.le]
    obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hab
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hdc
    simp only [hab, hcd, iff_false, not_true_eq_false, ite_false,
      Nat.add_sub_cancel_left]
    have : c + q + 1 - c = q + 1 := by omega
    rw [this]
    ring
  · have hba : a < b := Nat.lt_of_not_le hab
    rw [Nat.dist_eq_sub_of_le hba.le, Nat.dist_eq_sub_of_le_right hcd]
    obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_lt hba
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hcd
    simp only [hab, hcd, false_iff, not_true_eq_false, ite_false,
      Nat.add_sub_cancel_left]
    have : a + p + 1 - a = p + 1 := by omega
    rw [this]
    ring
  · have hba : a < b := Nat.lt_of_not_le hab
    have hdc : c < d := Nat.lt_of_not_le hcd
    rw [Nat.dist_eq_sub_of_le hba.le, Nat.dist_eq_sub_of_le hdc.le]
    obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_lt hba
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hdc
    simp only [hab, hcd, iff_self, ite_true]
    have hp : a + p + 1 - a = p + 1 := by omega
    have hq : c + q + 1 - c = q + 1 := by omega
    rw [hp, hq]
    have : a * c + (a + p + 1) * (c + q + 1) - (p + 1) * (q + 1) + (p + 1) * (q + 1) =
        a * (c + q + 1) + (a + p + 1) * c + (p + 1) * (q + 1) := by
      rw [Nat.sub_add_cancel (by nlinarith)]
      ring
    omega

/-- **Correctness of Karatsuba multiplication.** For all natural numbers $B$, $n$, $x$ and $y$,
Karatsuba multiplication of $x$ and $y$ as $n$-digit numbers in base $B$ returns $xy$.

The inputs need not be below $B^n$: the digit count only steers the recursion. -/
theorem karatsuba_ret (B n x y : ℕ) : (karatsuba B n x y).ret = x * y := by
  induction n using Nat.strong_induction_on generalizing x y with
  | _ n ih =>
    rw [karatsuba]
    split_ifs with hn
    · simp
    · have hm : (n + 1) / 2 < n := by omega
      simp only [ret_bind, ret_pure, ih _ hm]
      rw [karatsuba_middle]
      set m := (n + 1) / 2
      conv_rhs => rw [← Nat.div_add_mod x (B ^ m), ← Nat.div_add_mod y (B ^ m)]
      ring

/-! ## Operand sizes -/

/-- **Size bound for Karatsuba's recursive operands.** Let $B \ge 1$ and $n$ be natural numbers,
let $m = \lceil n/2 \rceil$, and let $x < B^n$ be a natural number. Then the high part
$\lfloor x / B^m \rfloor$, the low part $x \bmod B^m$, and their distance
$|\lfloor x / B^m \rfloor - x \bmod B^m|$ are all less than $B^m$.

Applied to both inputs, all six recursive operands stay within the digit model, and the base case
multiplies single digits. -/
theorem karatsuba_operands_lt {B n x : ℕ} (hB : 0 < B) (hx : x < B ^ n) :
    x / B ^ ((n + 1) / 2) < B ^ ((n + 1) / 2) ∧ x % B ^ ((n + 1) / 2) < B ^ ((n + 1) / 2) ∧
      Nat.dist (x / B ^ ((n + 1) / 2)) (x % B ^ ((n + 1) / 2)) < B ^ ((n + 1) / 2) := by
  set m := (n + 1) / 2
  have hpos : 0 < B ^ m := Nat.pow_pos hB
  have hdiv : x / B ^ m < B ^ m := by
    rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add]
    exact hx.trans_le (Nat.pow_le_pow_right hB (by omega))
  have hmod : x % B ^ m < B ^ m := Nat.mod_lt _ hpos
  refine ⟨hdiv, hmod, ?_⟩
  rw [Nat.dist_eq_max_sub_min]
  exact lt_of_le_of_lt (Nat.sub_le _ _) (max_lt hdiv hmod)

/-! ## Cost -/

/-- **Cost of Karatsuba multiplication.** For all natural numbers $B$, $n$, $x$ and $y$, the cost
of Karatsuba multiplication of $x$ and $y$ as $n$-digit numbers in base $B$ equals $T(n)$, where
$T$ is the Karatsuba cost recurrence, $T(n) = 1$ for $n \le 1$ and
$T(n) = 3\,T(\lceil n/2 \rceil) + n$ for $n \ge 2$.

In particular the cost depends only on the digit count $n$, not on $B$, $x$ or $y$. -/
theorem karatsuba_time (B n x y : ℕ) : (karatsuba B n x y).time = karatsubaCost n := by
  induction n using Nat.strong_induction_on generalizing x y with
  | _ n ih =>
    rw [karatsuba, karatsubaCost]
    split_ifs with hn
    · simp
    · have hm : (n + 1) / 2 < n := by omega
      simp only [time_bind, time_tick, time_pure, ih _ hm]
      ring

theorem karatsubaCost_of_le_one {n : ℕ} (hn : n ≤ 1) : karatsubaCost n = 1 := by
  rw [karatsubaCost]
  simp only [hn, ite_true]

theorem karatsubaCost_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    karatsubaCost n = 3 * karatsubaCost ((n + 1) / 2) + n := by
  rw [karatsubaCost]
  simp only [show ¬ n ≤ 1 by omega, ite_false]

/-- **Karatsuba cost at powers of two.** Let $T$ be the Karatsuba cost recurrence, $T(n) = 1$ for
$n \le 1$ and $T(n) = 3\,T(\lceil n/2 \rceil) + n$ for $n \ge 2$. For every natural number $k$,
$T(2^k) + 2^{k+1} = 3^{k+1}$.

So at $n = 2^k$ digits the cost is exactly $3^{k+1} - 2^{k+1} = 3\, n^{\log_2 3} - 2n$. -/
theorem karatsubaCost_two_pow (k : ℕ) : karatsubaCost (2 ^ k) + 2 ^ (k + 1) = 3 ^ (k + 1) := by
  induction k with
  | zero => simp [karatsubaCost_of_le_one]
  | succ k ih =>
      have h2 : 2 ≤ 2 ^ (k + 1) := Nat.le_self_pow (by omega) 2 |>.trans' (by norm_num)
      rw [karatsubaCost_of_two_le h2]
      have : (2 ^ (k + 1) + 1) / 2 = 2 ^ k := by rw [pow_succ]; omega
      rw [this, pow_succ 3 (k + 1), pow_succ 2 (k + 1), pow_succ 2 k]
      rw [pow_succ 2 k] at ih
      omega

theorem karatsubaCost_mono {n n' : ℕ} (h : n ≤ n') : karatsubaCost n ≤ karatsubaCost n' := by
  induction n' using Nat.strong_induction_on generalizing n with
  | _ n' ih =>
    by_cases hn : n ≤ 1
    · rw [karatsubaCost_of_le_one hn]
      unfold karatsubaCost
      split_ifs <;> omega
    · have h2 : 2 ≤ n' := by omega
      rw [karatsubaCost_of_two_le (show 2 ≤ n by omega), karatsubaCost_of_two_le h2]
      have hlt : (n' + 1) / 2 < n' := by omega
      have hle : (n + 1) / 2 ≤ (n' + 1) / 2 := by omega
      have := ih _ hlt hle
      omega

/-- **Power-of-three bound on the Karatsuba cost recurrence.** Let $T$ be the Karatsuba cost
recurrence, $T(n) = 1$ for $n \le 1$ and $T(n) = 3\,T(\lceil n/2 \rceil) + n$ for $n \ge 2$, and
let $\ell(n)$ be the least natural number $k$ with $n \le 2^k$ (so
$\ell(n) = \lceil \log_2 n \rceil$ for $n \ge 1$). For every natural number $n$,
$T(n) \le 3^{\ell(n) + 1}$.

The proof pads $n$ up to the next power of two. -/
theorem karatsubaCost_le (n : ℕ) : karatsubaCost n ≤ 3 ^ (Nat.clog 2 n + 1) := by
  have h := karatsubaCost_two_pow (Nat.clog 2 n)
  have := karatsubaCost_mono (Nat.le_pow_clog (by norm_num : 1 < 2) n)
  have : 0 < 2 ^ (Nat.clog 2 n + 1) := Nat.pow_pos (by norm_num)
  omega

/-- **Power-of-three bound on the cost of Karatsuba multiplication.** Let $\ell(n)$ be the least
natural number $k$ with $n \le 2^k$ (so $\ell(n) = \lceil \log_2 n \rceil$ for $n \ge 1$). For all
natural numbers $B$, $n$, $x$ and $y$, the cost of Karatsuba multiplication of $x$ and $y$ as
$n$-digit numbers in base $B$ is at most $3^{\ell(n) + 1}$. -/
theorem karatsuba_time_le (B n x y : ℕ) :
    (karatsuba B n x y).time ≤ 3 ^ (Nat.clog 2 n + 1) := by
  rw [karatsuba_time]
  exact karatsubaCost_le n

/-- **The $n^{\log_2 3}$ bound for the Karatsuba cost recurrence.** Let $T$ be the Karatsuba cost
recurrence, $T(n) = 1$ for $n \le 1$ and $T(n) = 3\,T(\lceil n/2 \rceil) + n$ for $n \ge 2$. For
every natural number $n \ge 1$, $T(n) \le 9\, n^{\log_2 3}$. -/
theorem karatsubaCost_le_rpow {n : ℕ} (hn : 1 ≤ n) :
    (karatsubaCost n : ℝ) ≤ 9 * (n : ℝ) ^ Real.logb 2 3 := by
  have hk := karatsubaCost_le n
  set k := Nat.clog 2 n with hkdef
  have hpow : 2 ^ (k - 1) ≤ n := by
    rcases Nat.lt_or_ge 1 n with h | h
    · exact (Nat.pow_pred_clog_lt_self (by norm_num) h).le
    · have : n = 1 := by omega
      subst this
      simp [hkdef]
  have h3 : (3 : ℝ) ^ (k - 1) ≤ (n : ℝ) ^ Real.logb 2 3 := by
    have : ((2 : ℝ) ^ (k - 1)) ^ Real.logb 2 3 = 3 ^ (k - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
        Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
        Real.rpow_natCast]
    rw [← this]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hpow)
      (Real.logb_nonneg (by norm_num) (by norm_num))
  have h9 : (3 : ℝ) ^ (k + 1) ≤ 9 * 3 ^ (k - 1) := by
    rcases k with _ | k
    · norm_num
    · simp only [Nat.add_sub_cancel, pow_succ]
      nlinarith [pow_pos (by norm_num : (0:ℝ) < 3) k]
  calc (karatsubaCost n : ℝ) ≤ 3 ^ (k + 1) := by exact_mod_cast hk
    _ ≤ 9 * 3 ^ (k - 1) := h9
    _ ≤ 9 * (n : ℝ) ^ Real.logb 2 3 := by gcongr

/-- **The $n^{\log_2 3}$ bound for Karatsuba multiplication.** For all natural numbers $B$, $x$,
$y$ and $n \ge 1$, the cost of Karatsuba multiplication of $x$ and $y$ as $n$-digit numbers in
base $B$ is at most $9\, n^{\log_2 3}$. -/
theorem karatsuba_time_le_rpow (B : ℕ) {n : ℕ} (hn : 1 ≤ n) (x y : ℕ) :
    ((karatsuba B n x y).time : ℝ) ≤ 9 * (n : ℝ) ^ Real.logb 2 3 := by
  rw [karatsuba_time]
  exact karatsubaCost_le_rpow hn

end Cslib.Algorithms.Lean.TimeM
