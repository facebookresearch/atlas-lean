/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Log
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Binary floating point: round to nearest, ties to even

A model of IEEE 754 binary arithmetic (Higham, *Accuracy and Stability of Numerical Algorithms*,
second edition, Chapter 2, with Theorem 2.2 for the relative error bound; Goldberg, *What every
computer scientist should know about floating-point arithmetic*, 1991; Sterbenz, *Floating-Point
Computation*, 1974, for the exact subtraction). A binary floating-point number with a `p`-bit
significand is `m 2^e` with `|m| < 2^p` (`IsFloat p`); a bounded format also limits the exponent `e`
of the last place to `[qmin, qmax]` (`IsFloatIn p qmin qmax`: zero, the subnormal and the normal
numbers). `fl p x` rounds a number of a linearly ordered field with a floor (`ℝ`, or `ℚ` for
execution) to nearest, ties to even: scale `x` so that its last place is the units digit (`ulpExp`),
round to the nearest integer with ties to the even one (`rne`), and scale back.

## Main results

* `abs_rne_sub_le`, `abs_rne_sub_le_half`, `even_rne_of_abs_sub_eq_half`: `rne` rounds to a
  nearest integer, within `1/2`, choosing the even integer on a tie.
* `isFloat_fl`, `abs_fl_sub_le_of_isFloat`, `even_of_abs_fl_sub_eq`, `fl_eq_self`: `fl x` is a
  floating-point number and a nearest one to `x`; on a tie its significand is even; floating-point
  numbers round to themselves.
* `abs_fl_sub_le`: **the relative error bound** `|fl x - x| ≤ u |x|` with unit roundoff
  `u = 2^(-p)`, for every `x` (there is no underflow or overflow with an unbounded exponent).
* `isFloatIn_fl`, `abs_fl_sub_le_of_isFloatIn`: **in the normal range** of a bounded format, from
  the smallest normal number `2^(qmin + p - 1)` to the largest finite number `(2^p - 1) 2^qmax`,
  `fl x` lies in the format and is a nearest number of it, so rounding in the format is `fl`, with
  relative error at most `u`.
* `isFloat_sub`, `isFloatIn_sub`, `fl_sub_eq_sub`: **Sterbenz's lemma**: if `y / 2 ≤ x ≤ 2 y`,
  then `x - y` is a floating-point number (of the same bounded format, subnormals included), so
  floating-point subtraction of `x` and `y` is exact.

## Cost model

None: these are statements about the values computed, not about the cost of computing them.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloatingPoint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-! ## Rounding to an integer -/

/-- **Nearest-integer rounding with ties to even.** For $m$ in a linearly ordered field $K$ with a
floor function, $\operatorname{rne}(m)$ is the integer $\lfloor m \rfloor$ if
$m - \lfloor m \rfloor < 1/2$, the integer $\lfloor m \rfloor + 1$ if
$m - \lfloor m \rfloor > 1/2$, and, when $m - \lfloor m \rfloor = 1/2$, whichever of
$\lfloor m \rfloor$ and $\lfloor m \rfloor + 1$ is even. -/
def rne (m : K) : ℤ :=
  if m - ⌊m⌋ < 1 / 2 then ⌊m⌋
  else if 1 / 2 < m - ⌊m⌋ then ⌊m⌋ + 1
  else if Even ⌊m⌋ then ⌊m⌋ else ⌊m⌋ + 1

/-- **Rounding error bounded by the distances to neighbouring integers.** Let $K$ be a linearly
ordered field with a floor function. For every $m \in K$, the integer $\operatorname{rne}(m)$
obtained by rounding $m$ to the nearest integer, ties to even, satisfies
$|\operatorname{rne}(m) - m| \le m - \lfloor m \rfloor$ and
$|\operatorname{rne}(m) - m| \le \lfloor m \rfloor + 1 - m$. -/
theorem abs_rne_sub_le_min (m : K) :
    |(rne m : K) - m| ≤ m - ⌊m⌋ ∧ |(rne m : K) - m| ≤ ⌊m⌋ + 1 - m := by
  have h0 := Int.floor_le m
  have h1 := Int.lt_floor_add_one m
  unfold rne
  split_ifs with ha hb hc
  · rw [abs_of_nonpos (by linarith)]
    constructor <;> linarith
  · push_cast
    rw [abs_of_nonneg (by linarith)]
    constructor <;> linarith
  · rw [abs_of_nonpos (by linarith)]
    constructor <;> linarith
  · push_cast
    rw [abs_of_nonneg (by linarith)]
    constructor <;> linarith

/-- **Round to nearest integer.** Let $K$ be a linearly ordered field with a floor function. For
every $m \in K$ and every integer $k$, the integer $\operatorname{rne}(m)$ obtained by rounding
$m$ to the nearest integer, ties to even, satisfies $|\operatorname{rne}(m) - m| \le |k - m|$:
no integer is closer to $m$ than $\operatorname{rne}(m)$. -/
theorem abs_rne_sub_le (m : K) (k : ℤ) : |(rne m : K) - m| ≤ |(k : K) - m| := by
  obtain ⟨h₁, h₂⟩ := abs_rne_sub_le_min m
  rcases le_or_gt k ⌊m⌋ with hk | hk
  · have : (k : K) ≤ ⌊m⌋ := by exact_mod_cast hk
    rw [abs_of_nonpos (show (k : K) - m ≤ 0 by linarith [Int.floor_le m])]
    linarith
  · have : (⌊m⌋ : K) + 1 ≤ k := by exact_mod_cast hk
    rw [abs_of_nonneg (show 0 ≤ (k : K) - m by linarith [Int.lt_floor_add_one m])]
    linarith

/-- **Rounding to the nearest integer is within one half.** Let $K$ be a linearly ordered field
with a floor function. For every $m \in K$, the integer $\operatorname{rne}(m)$ obtained by
rounding $m$ to the nearest integer, ties to even, satisfies
$|\operatorname{rne}(m) - m| \le 1/2$. -/
theorem abs_rne_sub_le_half (m : K) : |(rne m : K) - m| ≤ 1 / 2 := by
  obtain ⟨h₁, h₂⟩ := abs_rne_sub_le_min m
  by_contra h
  push Not at h
  linarith

/-- **Ties to even for the nearest integer.** Let $K$ be a linearly ordered field with a floor
function, let $m \in K$, and let $\operatorname{rne}(m)$ be the integer obtained by rounding $m$
to the nearest integer, ties to even. If $|\operatorname{rne}(m) - m| = 1/2$, that is, $m$ is
halfway between two consecutive integers, then $\operatorname{rne}(m)$ is even. -/
theorem even_rne_of_abs_sub_eq_half {m : K} (h : |(rne m : K) - m| = 1 / 2) : Even (rne m) := by
  have h0 := Int.floor_le m
  have h1 := Int.lt_floor_add_one m
  unfold rne at h ⊢
  split_ifs at h ⊢ with ha hb hc
  · rw [abs_of_nonpos (by linarith)] at h
    linarith
  · push_cast at h
    rw [abs_of_nonneg (by linarith)] at h
    linarith
  · exact hc
  · exact (Int.not_even_iff_odd.1 hc).add_one

theorem rne_intCast (k : ℤ) : rne (k : K) = k := by
  have h := abs_rne_sub_le (k : K) k
  rw [sub_self, abs_zero] at h
  have h' : ((rne (k : K) : ℤ) : K) = k := by
    have := abs_nonneg ((rne (k : K) : K) - k)
    linarith [abs_eq_zero.1 (le_antisymm h this)]
  exact_mod_cast h'

/-- **Rounding to nearest preserves integer upper bounds.** Let $K$ be a linearly ordered field
with a floor function, let $m \in K$ and let $k$ be an integer. If $m \le k$, then
$\operatorname{rne}(m) \le k$, where $\operatorname{rne}(m)$ is $m$ rounded to the nearest
integer with ties to even. -/
theorem rne_le_of_le {m : K} {k : ℤ} (h : m ≤ k) : rne m ≤ k := by
  by_contra hlt
  push Not at hlt
  have h₁ : (k : K) + 1 ≤ rne m := by exact_mod_cast hlt
  have := abs_rne_sub_le m k
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at this
  linarith

/-- **Rounding to nearest preserves integer lower bounds.** Let $K$ be a linearly ordered field
with a floor function, let $m \in K$ and let $k$ be an integer. If $k \le m$, then
$k \le \operatorname{rne}(m)$, where $\operatorname{rne}(m)$ is $m$ rounded to the nearest
integer with ties to even. -/
theorem le_rne_of_le {m : K} {k : ℤ} (h : (k : K) ≤ m) : k ≤ rne m := by
  by_contra hlt
  push Not at hlt
  have h₁ : (rne m : K) + 1 ≤ k := by exact_mod_cast hlt
  have := abs_rne_sub_le m k
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at this
  linarith

/-! ## Floating-point numbers and rounding -/

variable (p : ℕ)

/-- **Binary floating-point numbers.** For a natural number $p$, an element $x$ of a linearly
ordered field with a floor function is a binary floating-point number with a $p$-bit significand
and unbounded exponent when $x = m \cdot 2^e$ for some integers $m$ and $e$ with $|m| < 2^p$. -/
def IsFloat (x : K) : Prop := ∃ m e : ℤ, |m| < 2 ^ p ∧ x = m * 2 ^ e

/-- **Floating-point numbers of a bounded format.** For a natural number $p$ and integers
$q_{\min}$ and $q_{\max}$, an element $x$ of a linearly ordered field with a floor function is a
number of the binary format with $p$-bit significands and last-place exponents in
$[q_{\min}, q_{\max}]$ when $x = m \cdot 2^e$ for some integers $m$ and $e$ with $|m| < 2^p$ and
$q_{\min} \le e \le q_{\max}$. These are zero, the subnormal numbers and the normal numbers of
the format.

In IEEE 754 terms, $q_{\min} = e_{\min} - p + 1$ and $q_{\max} = e_{\max} - p + 1$. -/
def IsFloatIn (qmin qmax : ℤ) (x : K) : Prop :=
  ∃ m e : ℤ, |m| < 2 ^ p ∧ qmin ≤ e ∧ e ≤ qmax ∧ x = m * 2 ^ e

omit [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K] in
variable {p} in
theorem IsFloatIn.isFloat {qmin qmax : ℤ} {x : K} (h : IsFloatIn p qmin qmax x) :
    IsFloat p x := by
  obtain ⟨m, e, hm, -, -, rfl⟩ := h
  exact ⟨m, e, hm, rfl⟩

/-- **Exponent of the last place.** For a natural number $p$ (the significand length) and $x$ in a
linearly ordered field $K$ with a floor function, the exponent of the last place of $x$ is the
integer $\lfloor \log_2 |x| \rfloor - (p - 1)$. Here $\lfloor \log_2 |x| \rfloor$ is the integer
logarithm: the largest integer $n$ with $2^n \le |x|$ when $x \ne 0$, and $0$ when $x = 0$. -/
def ulpExp (x : K) : ℤ := Int.log 2 |x| - ((p : ℤ) - 1)

/-- **Round to nearest, ties to even.** For a natural number $p$ and an element $x$ of a linearly
ordered field with a floor function, let $e$ be the exponent of the last place of $x$ at precision
$p$, and let $\operatorname{rne}$ round to the nearest integer with ties to the even one. The
rounding of $x$ to nearest, ties to even, is
$\mathrm{fl}_p(x) = \operatorname{rne}(x / 2^e) \cdot 2^e$: scale $x$ so that its last place is the
units digit, round to the nearest integer with ties to even, and scale back. -/
def fl (x : K) : K := rne (x / 2 ^ ulpExp p x) * 2 ^ ulpExp p x

variable {p}

theorem two_zpow_pos (e : ℤ) : (0 : K) < 2 ^ e := zpow_pos two_pos e

/-- **Bounds on the scaled significand.** Let $K$ be a linearly ordered field with a floor
function, let $p \ge 1$ be a natural number and let $x \in K$ be nonzero. Let
$e = \lfloor \log_2 |x| \rfloor - (p - 1)$ be the exponent of the last place of $x$ for
$p$-bit significands. Then $2^{p-1} \le |x / 2^e|$ and $|x / 2^e| < 2^p$. -/
theorem scaled_bounds (hp : 1 ≤ p) {x : K} (hx : x ≠ 0) :
    (2 : K) ^ (p - 1) ≤ |x / 2 ^ ulpExp p x| ∧ |x / 2 ^ ulpExp p x| < 2 ^ p := by
  have hax : 0 < |x| := abs_pos.2 hx
  have hL₁ : (2 : K) ^ Int.log 2 |x| ≤ |x| := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) hax
    simpa using this
  have hL₂ : |x| < (2 : K) ^ (Int.log 2 |x| + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) |x|
    simpa using this
  have he := two_zpow_pos (K := K) (ulpExp p x)
  rw [abs_div, abs_of_pos he, le_div_iff₀ he, div_lt_iff₀ he]
  have h₁ : (2 : K) ^ (p - 1) * 2 ^ ulpExp p x = 2 ^ Int.log 2 |x| := by
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero, ulpExp]
    congr 1
    push_cast [Nat.cast_sub hp]
    ring
  have h₂ : (2 : K) ^ p * 2 ^ ulpExp p x = 2 ^ (Int.log 2 |x| + 1) := by
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero, ulpExp]
    congr 1
    ring
  rw [h₁, h₂]
  exact ⟨hL₁, hL₂⟩

/-- **The rounding error at the scale of the last place.** Let $x$ be an element of a linearly
ordered field with a floor function, let $p$ be a natural number, and let $e$ be the exponent of
the last place of $x$ at precision $p$. Writing $\operatorname{rne}$ for rounding to the nearest
integer with ties to even, the rounding $\mathrm{fl}_p(x)$ of $x$ to nearest, ties to even, at
precision $p$ has the error
$\mathrm{fl}_p(x) - x = (\operatorname{rne}(x / 2^e) - x / 2^e) \cdot 2^e$. -/
theorem fl_sub_eq (x : K) :
    fl p x - x = ((rne (x / 2 ^ ulpExp p x) : K) - x / 2 ^ ulpExp p x) * 2 ^ ulpExp p x := by
  have he := (two_zpow_pos (K := K) (ulpExp p x)).ne'
  rw [fl, sub_mul, div_mul_cancel₀ _ he]

theorem abs_fl_sub_eq (x : K) :
    |fl p x - x| = |(rne (x / 2 ^ ulpExp p x) : K) - x / 2 ^ ulpExp p x| * 2 ^ ulpExp p x := by
  rw [fl_sub_eq, abs_mul, abs_of_pos (two_zpow_pos (K := K) (ulpExp p x))]

theorem fl_zero : fl p (0 : K) = 0 := by
  have : rne (0 : K) = 0 := by exact_mod_cast rne_intCast (K := K) 0
  simp [fl, this]

/-- **The relative error bound.** Let $K$ be a linearly ordered field with a floor function and
let $p$ be a natural number. For every $x \in K$, the rounding $\mathrm{fl}(x)$ of $x$ to
nearest, ties to even, with $p$-bit significands satisfies
$|\mathrm{fl}(x) - x| \le u\,|x|$, where $u = 2^{-p}$ is the unit roundoff.

The exponent is unbounded, so the bound holds for every $x$, with no underflow or overflow. -/
theorem abs_fl_sub_le (x : K) : |fl p x - x| ≤ 2 ^ (-(p : ℤ)) * |x| := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [fl_zero]
  have hax : 0 < |x| := abs_pos.2 hx
  have hL₁ : (2 : K) ^ Int.log 2 |x| ≤ |x| := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) hax
    simpa using this
  rw [abs_fl_sub_eq]
  have h := abs_rne_sub_le_half (x / 2 ^ ulpExp p x)
  have he := two_zpow_pos (K := K) (ulpExp p x)
  calc |(rne (x / 2 ^ ulpExp p x) : K) - x / 2 ^ ulpExp p x| * 2 ^ ulpExp p x
      ≤ 1 / 2 * 2 ^ ulpExp p x := mul_le_mul_of_nonneg_right h he.le
    _ = 2 ^ (-(p : ℤ)) * 2 ^ Int.log 2 |x| := by
        rw [← zpow_add₀ two_ne_zero, ulpExp, one_div, ← zpow_neg_one, ← zpow_add₀ two_ne_zero]
        congr 1
        ring
    _ ≤ 2 ^ (-(p : ℤ)) * |x| := mul_le_mul_of_nonneg_left hL₁ (two_zpow_pos _).le

/-- **Round to nearest for floating-point numbers.** Let $K$ be a linearly ordered field with a
floor function and let $p \ge 1$. For every $x \in K$ and every binary floating-point number
$f \in K$ with a $p$-bit significand (and unbounded exponent), the rounding $\mathrm{fl}(x)$ of
$x$ to nearest, ties to even, with $p$-bit significands satisfies
$|\mathrm{fl}(x) - x| \le |f - x|$: no floating-point number is closer to $x$ than
$\mathrm{fl}(x)$. -/
theorem abs_fl_sub_le_of_isFloat (hp : 1 ≤ p) (x : K) {f : K} (hf : IsFloat p f) :
    |fl p x - x| ≤ |f - x| := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [fl_zero]
  obtain ⟨n, d, hn, rfl⟩ := hf
  set e := ulpExp p x with he_def
  set M := x / 2 ^ e with hM
  have he := two_zpow_pos (K := K) e
  obtain ⟨hM₁, hM₂⟩ := scaled_bounds hp hx
  rw [← he_def, ← hM] at hM₁ hM₂
  rw [abs_fl_sub_eq, ← he_def, ← hM]
  -- `f - x = (f / 2^e - M) 2^e`
  have hfx : (n : K) * 2 ^ d - x = ((n : K) * 2 ^ d / 2 ^ e - M) * 2 ^ e := by
    rw [sub_mul, div_mul_cancel₀ _ he.ne', hM, div_mul_cancel₀ _ he.ne']
  rw [hfx, abs_mul, abs_of_pos he]
  refine mul_le_mul_of_nonneg_right ?_ he.le
  rcases le_or_gt e d with hed | hed
  · -- `f` is an integer multiple of `2^e`
    have hk : (n : K) * 2 ^ d / 2 ^ e = ((n * 2 ^ (d - e).toNat : ℤ) : K) := by
      rw [mul_div_assoc, ← zpow_sub₀ two_ne_zero]
      push_cast
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
    rw [hk]
    exact abs_rne_sub_le M _
  · -- `f` is below the binade of `x`: the binade's edge `± 2^(p-1)` is closer
    have hF : |(n : K) * 2 ^ d / 2 ^ e| < 2 ^ (p - 1) := by
      rw [mul_div_assoc, ← zpow_sub₀ two_ne_zero, abs_mul,
        abs_of_pos (two_zpow_pos (K := K) (d - e))]
      have hn' : |(n : K)| < 2 ^ p := by exact_mod_cast hn
      have hde : (2 : K) ^ (d - e) ≤ 1 / 2 := by
        rw [one_div, ← zpow_neg_one]
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h2 : (2 : K) ^ p = 2 * 2 ^ (p - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hp]
      calc |(n : K)| * 2 ^ (d - e) ≤ |(n : K)| * (1 / 2) :=
            mul_le_mul_of_nonneg_left hde (abs_nonneg _)
        _ < 2 ^ p * (1 / 2) := mul_lt_mul_of_pos_right hn' (by norm_num)
        _ = 2 ^ (p - 1) := by rw [h2]; ring
    set k : ℤ := if 0 ≤ M then 2 ^ (p - 1) else -2 ^ (p - 1) with hk
    have hkM : |(k : K) - M| = |M| - 2 ^ (p - 1) := by
      rw [hk]
      split_ifs with hM0
      · rw [abs_of_nonneg hM0] at hM₁ ⊢
        push_cast
        rw [abs_of_nonpos (by linarith)]
        ring
      · push Not at hM0
        rw [abs_of_neg hM0] at hM₁ ⊢
        push_cast
        rw [abs_of_nonneg (by linarith)]
        ring
    calc |(rne M : K) - M| ≤ |(k : K) - M| := abs_rne_sub_le M k
      _ = |M| - 2 ^ (p - 1) := hkM
      _ ≤ |M| - |(n : K) * 2 ^ d / 2 ^ e| := by linarith
      _ ≤ |(n : K) * 2 ^ d / 2 ^ e - M| := by
          have := abs_sub_abs_le_abs_sub M ((n : K) * 2 ^ d / 2 ^ e)
          rw [abs_sub_comm] at this
          linarith

/-- **Floating-point numbers round to themselves.** Let $p \ge 1$ and let $x$ be an element of a
linearly ordered field with a floor function. If $x$ is a binary floating-point number with a
$p$-bit significand, that is, $x = m \cdot 2^e$ for some integers $m$ and $e$ with $|m| < 2^p$,
then rounding $x$ to nearest, ties to even, at precision $p$ returns $x$: $\mathrm{fl}_p(x) = x$. -/
theorem fl_eq_self (hp : 1 ≤ p) {x : K} (hx : IsFloat p x) : fl p x = x := by
  have h := abs_fl_sub_le_of_isFloat hp x hx
  rw [sub_self, abs_zero] at h
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h)

/-- **Ties to even for floating-point rounding.** Let $K$ be a linearly ordered field with a floor
function, let $p$ be a natural number, let $x \in K$, and let $e$ be the exponent of the last
place of $x$, which is $\lfloor \log_2 |x| \rfloor - (p - 1)$ for $x \ne 0$. If the rounding
$\mathrm{fl}(x)$ of $x$ to nearest, ties to even, with $p$-bit significands satisfies
$|\mathrm{fl}(x) - x| = 2^e / 2$, then the integer $\operatorname{rne}(x / 2^e)$, the significand
of $\mathrm{fl}(x)$ at the last place of $x$, is even. -/
theorem even_of_abs_fl_sub_eq {x : K} (h : |fl p x - x| = 2 ^ ulpExp p x / 2) :
    Even (rne (x / 2 ^ ulpExp p x)) := by
  apply even_rne_of_abs_sub_eq_half
  have he := two_zpow_pos (K := K) (ulpExp p x)
  rw [abs_fl_sub_eq] at h
  have h' : |(rne (x / 2 ^ ulpExp p x) : K) - x / 2 ^ ulpExp p x| * 2 ^ ulpExp p x =
      1 / 2 * 2 ^ ulpExp p x := by rw [h]; ring
  exact mul_right_cancel₀ he.ne' h'

/-- **Bound on the rounded significand.** Let $K$ be a linearly ordered field with a floor
function, let $p \ge 1$, let $x \in K$ be nonzero, and let
$e = \lfloor \log_2 |x| \rfloor - (p - 1)$ be the exponent of the last place of $x$. Then
$|\operatorname{rne}(x / 2^e)| \le 2^p$, where $\operatorname{rne}$ rounds to the nearest
integer, ties to even.

Since $|x / 2^e| < 2^p$, the value $2^p$ occurs only when rounding carries into the next
binade. -/
theorem abs_rne_le (hp : 1 ≤ p) {x : K} (hx : x ≠ 0) :
    |rne (x / 2 ^ ulpExp p x)| ≤ 2 ^ p := by
  obtain ⟨-, h₂⟩ := scaled_bounds hp hx
  rw [abs_lt] at h₂
  rw [abs_le]
  constructor
  · exact le_rne_of_le (by push_cast; linarith)
  · exact rne_le_of_le (by push_cast; linarith)

/-- **Rounding gives a floating-point number.** Let $p \ge 1$. For every element $x$ of a linearly
ordered field with a floor function, the rounding $\mathrm{fl}_p(x)$ of $x$ to nearest, ties to
even, is a binary floating-point number with a $p$-bit significand: $\mathrm{fl}_p(x) = m \cdot 2^e$
for some integers $m$ and $e$ with $|m| < 2^p$. -/
theorem isFloat_fl (hp : 1 ≤ p) (x : K) : IsFloat p (fl p x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, 0, by simp [abs_zero], by simp [fl_zero]⟩
  have hr := abs_rne_le hp hx
  rcases hr.lt_or_eq with hlt | heq
  · exact ⟨_, _, hlt, rfl⟩
  · -- carry into the next binade: `± 2^p 2^e = ± 2^(p-1) 2^(e+1)`
    have h2 : (2 : ℤ) ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ', Nat.sub_add_cancel hp]
    have hlt : |(2 : ℤ) ^ (p - 1)| < 2 ^ p := by
      rw [abs_of_pos (by positivity), h2]
      have : (0 : ℤ) < 2 ^ (p - 1) := by positivity
      omega
    rcases abs_eq (by positivity) |>.1 heq with h | h
    · refine ⟨2 ^ (p - 1), ulpExp p x + 1, hlt, ?_⟩
      rw [fl, h, zpow_add_one₀ two_ne_zero]
      push_cast [h2]
      ring
    · refine ⟨-2 ^ (p - 1), ulpExp p x + 1, by rwa [abs_neg], ?_⟩
      rw [fl, h, zpow_add_one₀ two_ne_zero]
      push_cast [h2]
      ring

/-! ## The normal range of a bounded format -/

/-- **In the normal range, rounding stays in the format.** Let $p \ge 1$, let $q_{\min}$ and
$q_{\max}$ be integers, and let $x$ be an element of a linearly ordered field with a floor
function. If $2^{q_{\min} + p - 1} \le |x|$ ($x$ is at least the smallest normal number) and
$|x| \le (2^p - 1) \cdot 2^{q_{\max}}$ ($x$ is at most the largest finite number), then the
rounding $\mathrm{fl}_p(x)$ of $x$ to nearest, ties to even, is a number of the binary format
with $p$-bit significands whose last place has exponent in $[q_{\min}, q_{\max}]$.

Since $\mathrm{fl}_p(x)$ is also a nearest number of the format to $x$, with relative error at
most $2^{-p}$, rounding in the format in the normal range is the nearest-even rounding. -/
theorem isFloatIn_fl (hp : 1 ≤ p) {qmin qmax : ℤ} {x : K}
    (hlo : (2 : K) ^ (qmin + ((p : ℤ) - 1)) ≤ |x|) (hhi : |x| ≤ (2 ^ p - 1) * 2 ^ qmax) :
    IsFloatIn p qmin qmax (fl p x) := by
  have hax : 0 < |x| := lt_of_lt_of_le (two_zpow_pos _) hlo
  have hx : x ≠ 0 := abs_pos.1 hax
  have hlog₁ : qmin + ((p : ℤ) - 1) ≤ Int.log 2 |x| := by
    have := (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hax).1 (by simpa using hlo)
    exact this
  have hlt : |x| < (2 : K) ^ (qmax + p) := by
    rw [zpow_add₀ two_ne_zero, zpow_natCast, mul_comm]
    have := two_zpow_pos (K := K) qmax
    nlinarith
  have hlog₂ : Int.log 2 |x| < qmax + p :=
    (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hax).1 (by simpa using hlt)
  have he₁ : qmin ≤ ulpExp p x := by unfold ulpExp; omega
  have he₂ : ulpExp p x ≤ qmax := by unfold ulpExp; omega
  rcases (abs_rne_le hp hx).lt_or_eq with hr | hr
  · exact ⟨_, _, hr, he₁, he₂, rfl⟩
  · -- a carry into the next binade cannot overflow
    have he₃ : ulpExp p x + 1 ≤ qmax := by
      by_contra hcon
      have hq : ulpExp p x = qmax := by omega
      have hM : |x / 2 ^ ulpExp p x| ≤ 2 ^ p - 1 := by
        rw [abs_div, abs_of_pos (two_zpow_pos (K := K) _), div_le_iff₀ (two_zpow_pos _), hq]
        exact hhi
      rw [abs_le] at hM
      have h₁ : rne (x / 2 ^ ulpExp p x) ≤ 2 ^ p - 1 := rne_le_of_le (by push_cast; linarith)
      have h₂ : -(2 ^ p - 1) ≤ rne (x / 2 ^ ulpExp p x) := le_rne_of_le (by push_cast; linarith)
      have : |rne (x / 2 ^ ulpExp p x)| ≤ 2 ^ p - 1 := abs_le.2 ⟨h₂, h₁⟩
      omega
    obtain ⟨m, e, hm, rfl, hfx⟩ : ∃ m e : ℤ, |m| < 2 ^ p ∧ e = ulpExp p x + 1 ∧
        fl p x = m * 2 ^ e := by
      have h2 : (2 : ℤ) ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ', Nat.sub_add_cancel hp]
      have hlt' : |(2 : ℤ) ^ (p - 1)| < 2 ^ p := by
        rw [abs_of_pos (by positivity), h2]
        have : (0 : ℤ) < 2 ^ (p - 1) := by positivity
        omega
      rcases abs_eq (by positivity) |>.1 hr with h | h
      · refine ⟨2 ^ (p - 1), _, hlt', rfl, ?_⟩
        rw [fl, h, zpow_add_one₀ two_ne_zero]
        push_cast [h2]
        ring
      · refine ⟨-2 ^ (p - 1), _, by rwa [abs_neg], rfl, ?_⟩
        rw [fl, h, zpow_add_one₀ two_ne_zero]
        push_cast [h2]
        ring
    exact ⟨m, ulpExp p x + 1, hm, by omega, he₃, hfx⟩

/-- **Round to nearest in a bounded format.** Let $K$ be a linearly ordered field with a floor
function, let $p \ge 1$, and let $q_{\min}$ and $q_{\max}$ be integers. For every $x \in K$ and
every number $f$ of the binary format with $p$-bit significands and last-place exponents in
$[q_{\min}, q_{\max}]$, the rounding $\mathrm{fl}(x)$ of $x$ to nearest, ties to even, with
$p$-bit significands satisfies $|\mathrm{fl}(x) - x| \le |f - x|$. -/
theorem abs_fl_sub_le_of_isFloatIn (hp : 1 ≤ p) (x : K) {qmin qmax : ℤ} {f : K}
    (hf : IsFloatIn p qmin qmax f) : |fl p x - x| ≤ |f - x| :=
  abs_fl_sub_le_of_isFloat hp x hf.isFloat

/-! ## Sterbenz's lemma -/

/-- **The difference of floating-point numbers within a factor of two.** Let $K$ be a linearly
ordered field with a floor function and let $p$ be a natural number. Let $x, y \in K$ and let
$m_x, m_y, e_x, e_y$ be integers with $|m_x| < 2^p$, $|m_y| < 2^p$, $x = m_x 2^{e_x}$ and
$y = m_y 2^{e_y}$. If $y / 2 \le x \le 2y$, then there is an integer $k$ with $|k| < 2^p$ and
$x - y = k \cdot 2^{\min(e_x, e_y)}$. -/
theorem exists_sub_eq_of_le {x y : K} {mx my ex ey : ℤ} (hmx : |mx| < 2 ^ p)
    (hmy : |my| < 2 ^ p) (hx : x = mx * 2 ^ ex) (hy : y = my * 2 ^ ey) (h₁ : y / 2 ≤ x)
    (h₂ : x ≤ 2 * y) : ∃ k : ℤ, |k| < 2 ^ p ∧ x - y = k * 2 ^ min ex ey := by
  set e := min ex ey with he
  set k : ℤ := mx * 2 ^ (ex - e).toNat - my * 2 ^ (ey - e).toNat with hk
  have hpos := two_zpow_pos (K := K) e
  have hxy : x - y = k * 2 ^ e := by
    rw [hk, hx, hy]
    push_cast
    rw [sub_mul, mul_assoc, mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ two_ne_zero,
      ← zpow_add₀ two_ne_zero, Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
    congr 2 <;> ring_nf
  refine ⟨k, ?_, hxy⟩
  -- `|x - y| ≤ x` and `|x - y| ≤ y`
  have hy0 : 0 ≤ y := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hdx : |x - y| ≤ x := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have hdy : |x - y| ≤ y := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have hkabs : |(k : K)| * 2 ^ e = |x - y| := by
    rw [hxy, abs_mul, abs_of_pos hpos]
  rcases min_choice ex ey with hmin | hmin
  · have hmx' : |(mx : K)| * 2 ^ e = x := by
      have h' : |x| = |(mx : K)| * 2 ^ ex := by
        rw [hx, abs_mul, abs_of_pos (two_zpow_pos (K := K) ex)]
      rw [abs_of_nonneg hx0] at h'
      rw [he, hmin, h']
    have : |(k : K)| ≤ |(mx : K)| := le_of_mul_le_mul_right (by rw [hkabs, hmx']; exact hdx) hpos
    have : |k| ≤ |mx| := by exact_mod_cast this
    omega
  · have hmy' : |(my : K)| * 2 ^ e = y := by
      have h' : |y| = |(my : K)| * 2 ^ ey := by
        rw [hy, abs_mul, abs_of_pos (two_zpow_pos (K := K) ey)]
      rw [abs_of_nonneg hy0] at h'
      rw [he, hmin, h']
    have : |(k : K)| ≤ |(my : K)| := le_of_mul_le_mul_right (by rw [hkabs, hmy']; exact hdy) hpos
    have : |k| ≤ |my| := by exact_mod_cast this
    omega

/-- **Sterbenz's lemma.** Let $p$ be a natural number and let $x$ and $y$ be binary floating-point
numbers with $p$-bit significands (and unbounded exponent) in a linearly ordered field with a
floor function. If $y / 2 \le x \le 2y$, then $x - y$ is also a binary floating-point number
with a $p$-bit significand. -/
theorem isFloat_sub {x y : K} (hx : IsFloat p x) (hy : IsFloat p y) (h₁ : y / 2 ≤ x)
    (h₂ : x ≤ 2 * y) : IsFloat p (x - y) := by
  obtain ⟨mx, ex, hmx, rfl⟩ := hx
  obtain ⟨my, ey, hmy, rfl⟩ := hy
  obtain ⟨k, hk, hsub⟩ := exists_sub_eq_of_le hmx hmy rfl rfl h₁ h₂
  exact ⟨k, _, hk, hsub⟩

/-- **Sterbenz's lemma in a bounded format.** Let $p$ be a natural number, let $q_{\min}$ and
$q_{\max}$ be integers, and let $x$ and $y$ be numbers of the binary format with $p$-bit
significands whose last place has exponent in $[q_{\min}, q_{\max}]$ (subnormal numbers
included), in a linearly ordered field with a floor function. If $y / 2 \le x \le 2y$, then
$x - y$ is also a number of this format. -/
theorem isFloatIn_sub {qmin qmax : ℤ} {x y : K} (hx : IsFloatIn p qmin qmax x)
    (hy : IsFloatIn p qmin qmax y) (h₁ : y / 2 ≤ x) (h₂ : x ≤ 2 * y) :
    IsFloatIn p qmin qmax (x - y) := by
  obtain ⟨mx, ex, hmx, hex₁, hex₂, rfl⟩ := hx
  obtain ⟨my, ey, hmy, hey₁, hey₂, rfl⟩ := hy
  obtain ⟨k, hk, hsub⟩ := exists_sub_eq_of_le hmx hmy rfl rfl h₁ h₂
  exact ⟨k, _, hk, le_min hex₁ hey₁, (min_le_left _ _).trans hex₂, hsub⟩

/-- **Floating-point subtraction is exact under Sterbenz's condition.** Let $p \ge 1$ and let $x$
and $y$ be binary floating-point numbers with $p$-bit significands in a linearly ordered field
with a floor function. If $y / 2 \le x \le 2y$, then rounding $x - y$ to nearest, ties to even,
at precision $p$ returns it exactly: $\mathrm{fl}_p(x - y) = x - y$. -/
theorem fl_sub_eq_sub (hp : 1 ≤ p) {x y : K} (hx : IsFloat p x) (hy : IsFloat p y)
    (h₁ : y / 2 ≤ x) (h₂ : x ≤ 2 * y) : fl p (x - y) = x - y :=
  fl_eq_self hp (isFloat_sub hx hy h₁ h₂)

end Cslib.Algorithms.Lean.FloatingPoint
