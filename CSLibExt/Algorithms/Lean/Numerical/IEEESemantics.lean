/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Numerical.FloatingPoint
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.EReal.Basic

/-!
# Total IEEE-style operation semantics with special values and exceptions

A model of IEEE 754 binary floating-point arithmetic with signed zeros, infinities, NaN and the
five status flags (IEEE Std 754-2019; Goldberg, *What every computer scientist should know about
floating-point arithmetic*, 1991, Sections 2.1–2.3 and 3.2; Boldo, Jourdan, Leroy and Melquiond,
*Verified compilation of floating-point computations*, Journal of Automated Reasoning 54(2), 2015,
Sections 5.1, 5.2 and 6.3), built on the bounded format `IsFloatIn` of
`CSLibExt.Algorithms.Lean.Numerical.FloatingPoint`.

* `BinaryFormat`: a precision `p ≥ 1` and last-place exponents in `[qmin, qmax]`, `qmin ≤ qmax`.
* `RoundingMode`, `RoundingMode.roundInt`, `RoundingMode.round`: round to nearest, ties to even,
  and the three directed rounding modes, and rounding at the last-place exponent
  `max (ulpExp p x) qmin`, which gives gradual underflow and leaves the exponent unbounded above,
  as Flocq's `round` does.
* `Value`: the canonical NaN, `±∞`, and finite numbers `±m` with a sign bit, so `+0 ≠ -0`.
* `Flags`, `roundResult`: the flags an operation raises, and the value an exact real result
  delivers: overflow by rounding mode, gradual underflow with tininess detected before rounding.
* `Operation.eval`: the total semantics of `+`, `-`, `×`, `÷` and `√`.
* `Value.compare`: the quiet four-outcome comparison (less, equal, greater, unordered).

## Main results

* `not_le_nan_and_not_isPartialOrder`: `NaN ≤ NaN` fails, so `≤` is not a partial order.
* `eval_add_comm`, `eval_mul_comm`: addition and multiplication are commutative, flags included.
* `not_add_assoc`: addition is not associative, in every format and rounding mode.
* `not_mul_assoc`: multiplication is not associative when `qmin ≤ -1` and `1 ≤ qmax`, as in
  binary32 and binary64.

## Scope

The model is canonical-NaN: one quiet NaN, with no sign, no payload and no signalling NaN. It
covers round to nearest, ties to even, and the three directed rounding modes, not
`roundTiesToAway`; tininess is detected before rounding; and comparison is the quiet one. Fused
multiply-add, remainder, conversions and trapping are not modelled.

## Why a separate model

In Lean's logic, `Float` and `Float32` are the core models `Float.Model` and `Float32.Model`:
binary64 and binary32 with round to nearest, ties to even, only, and no status flags. Their
documentation asks for a floating-point library to be developed separately and then related to
them. Mathlib's `FP.Float` is deprecated and also rounds only to nearest. This model covers every
binary format of the bounded-format API, four rounding modes and the flags, and rounds with the
rounding of `FloatingPoint` (`rne`, `ulpExp`, `fl`).

## Cost model

None: these are statements about the values computed, not about the cost of computing them.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloatingPoint.IEEE

/-! ## Formats and rounding -/

/-- **Binary floating-point format.** A binary format has a precision $p \ge 1$ (the number of
significand bits) and integers $q_{\min} \le q_{\max}$, the least and greatest exponents of the
last place. Its finite numbers are the numbers of the bounded format: $m \cdot 2^e$ with integers
$|m| < 2^p$ and $q_{\min} \le e \le q_{\max}$, which are zero, the subnormal numbers and the
normal numbers. In IEEE 754 terms, $q_{\min} = e_{\min} - p + 1$ and
$q_{\max} = e_{\max} - p + 1$; binary64 has $p = 53$, $q_{\min} = -1074$ and $q_{\max} = 971$.

Source: IEEE Std 754-2019; Goldberg, *What every computer scientist should know about floating-point
arithmetic*, ACM Computing Surveys 23(1), 1991, Section 2.1 (Table 1). -/
structure BinaryFormat where
  /-- The precision $p$, the number of significand bits. -/
  prec : ℕ
  /-- The least exponent $q_{\min}$ of the last place. -/
  qmin : ℤ
  /-- The greatest exponent $q_{\max}$ of the last place. -/
  qmax : ℤ
  /-- The precision is positive. -/
  one_le_prec : 1 ≤ prec
  /-- The exponent range is not empty. -/
  qmin_le_qmax : qmin ≤ qmax

/-- **Rounding modes.** The four rounding modes of IEEE 754 binary arithmetic: round to nearest with
ties to even, the default, and the three directed rounding modes the standard requires, toward
$+\infty$, toward $-\infty$ and toward zero.

Source: IEEE Std 754-2019; Goldberg, *What every computer scientist should know about floating-point
arithmetic*, ACM Computing Surveys 23(1), 1991, Section 2.3.2. -/
inductive RoundingMode where
  /-- Round to nearest, ties to even. -/
  | nearestEven
  /-- Round toward $+\infty$. -/
  | towardPositive
  /-- Round toward $-\infty$. -/
  | towardNegative
  /-- Round toward zero. -/
  | towardZero
  deriving DecidableEq

namespace RoundingMode

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- **Rounding to an integer in a rounding mode.** For $m$ in a linearly ordered field with a
floor function, $m$ rounds to the nearest integer with ties to even, $\operatorname{rne}(m)$, in
the mode to nearest; to $\lceil m \rceil$ toward $+\infty$; to $\lfloor m \rfloor$ toward
$-\infty$; and toward zero to $\lfloor m \rfloor$ if $m \ge 0$ and to $\lceil m \rceil$ if
$m < 0$. -/
def roundInt : RoundingMode → K → ℤ
  | nearestEven, m => rne m
  | towardPositive, m => ⌈m⌉
  | towardNegative, m => ⌊m⌋
  | towardZero, m => if 0 ≤ m then ⌊m⌋ else ⌈m⌉

/-- **Rounding in a bounded format.** Let $p$ be a natural number, $q_{\min}$ an integer and $r$ a
rounding mode. For $x$ in a linearly ordered field with a floor function, let
$e = \max(\lfloor \log_2 |x| \rfloor - (p - 1), q_{\min})$, where
$\lfloor \log_2 |x| \rfloor$ is the largest integer $n$ with $2^n \le |x|$ for $x \ne 0$ and is
$0$ for $x = 0$. The rounding of $x$ in mode $r$ is $R_r(x / 2^e) \cdot 2^e$, where $R_r$ rounds
to an integer in mode $r$: scale $x$ so that the last place of its $p$-bit significand, but no
place below $2^{q_{\min}}$, is the units digit, round to an integer in the mode, and scale back.

Capping $e$ below at $q_{\min}$ gives gradual underflow. For $p \ge 1$ and
$|x| < 2^{q_{\min} + p - 1}$, the smallest normal number, the result is a multiple of $2^{q_{\min}}$
of absolute value at most $2^{q_{\min} + p - 1}$: zero, a subnormal number, or
$\pm 2^{q_{\min} + p - 1}$ itself. The exponent is not bounded above, so the result can exceed the
largest finite number; in the mode to nearest and for $|x| \ge 2^{q_{\min} + p - 1}$, this is
$\mathrm{fl}_p(x)$.

Source: Boldo, Jourdan, Leroy and Melquiond, *Verified compilation of floating-point computations*,
Journal of Automated Reasoning 54(2), 2015, Section 5.2 (Flocq's rounding, with no upper bound on
the exponent). -/
def round (r : RoundingMode) (p : ℕ) (qmin : ℤ) (x : K) : K :=
  r.roundInt (x / 2 ^ max (ulpExp p x) qmin) * 2 ^ max (ulpExp p x) qmin

theorem roundInt_intCast (r : RoundingMode) (k : ℤ) : r.roundInt (k : K) = k := by
  cases r <;> simp [roundInt, rne_intCast]

theorem abs_roundInt_le (r : RoundingMode) {m : K} {N : ℤ} (h : |m| ≤ N) :
    |r.roundInt m| ≤ N := by
  rw [abs_le] at h ⊢
  obtain ⟨h₁, h₂⟩ := h
  have hfl : -N ≤ ⌊m⌋ ∧ ⌊m⌋ ≤ N :=
    ⟨Int.le_floor.2 (by push_cast; linarith), by exact_mod_cast (Int.floor_le m).trans h₂⟩
  have hce : -N ≤ ⌈m⌉ ∧ ⌈m⌉ ≤ N := by
    refine ⟨?_, Int.ceil_le.2 h₂⟩
    have : ((-N : ℤ) : K) ≤ ((⌈m⌉ : ℤ) : K) := by push_cast; linarith [Int.le_ceil m]
    exact_mod_cast this
  cases r with
  | nearestEven => exact ⟨le_rne_of_le (by push_cast; linarith), rne_le_of_le h₂⟩
  | towardPositive => exact hce
  | towardNegative => exact hfl
  | towardZero =>
    simp only [roundInt]
    split_ifs
    · exact hfl
    · exact hce

theorem abs_div_two_zpow_lt {p : ℕ} {e : ℤ} {x : K} (he : ulpExp p x ≤ e) :
    |x / 2 ^ e| < 2 ^ p := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hL : |x| < (2 : K) ^ (Int.log 2 |x| + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) |x|
    simpa using this
  have hpos := two_zpow_pos (K := K) e
  rw [abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
  calc |x| < 2 ^ (Int.log 2 |x| + 1) := hL
    _ ≤ 2 ^ ((p : ℤ) + e) :=
        zpow_le_zpow_right₀ (by norm_num) (by unfold ulpExp at he; omega)
    _ = 2 ^ p * 2 ^ e := by rw [zpow_add₀ two_ne_zero, zpow_natCast]

theorem round_zero (r : RoundingMode) (p : ℕ) (qmin : ℤ) : r.round p qmin (0 : K) = 0 := by
  have h := r.roundInt_intCast (K := K) 0
  simp only [Int.cast_zero] at h
  simp [round, h]

-- Numbers with a `p`-bit significand and a last place at or above `2 ^ qmin` round to
-- themselves in every mode.
theorem round_eq_self (r : RoundingMode) {p : ℕ} {qmin m d : ℤ} (hm : |m| < 2 ^ p)
    (hd : qmin ≤ d) : r.round p qmin ((m : K) * 2 ^ d) = m * 2 ^ d := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simpa using r.round_zero (K := K) p qmin
  have hpos := two_zpow_pos (K := K) d
  have hx : |(m : K) * 2 ^ d| < 2 ^ ((p : ℤ) + d) := by
    rw [abs_mul, abs_of_pos hpos, zpow_add₀ two_ne_zero, zpow_natCast]
    have : |(m : K)| < 2 ^ p := by exact_mod_cast hm
    exact mul_lt_mul_of_pos_right this hpos
  have hx0 : 0 < |(m : K) * 2 ^ d| :=
    abs_pos.2 (mul_ne_zero (by exact_mod_cast hm0) hpos.ne')
  have hlog : Int.log 2 |(m : K) * 2 ^ d| < (p : ℤ) + d :=
    (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hx0).1 (by simpa using hx)
  have hed : max (ulpExp p ((m : K) * 2 ^ d)) qmin ≤ d :=
    max_le (by unfold ulpExp; omega) hd
  set e := max (ulpExp p ((m : K) * 2 ^ d)) qmin with he
  have hk : (m : K) * 2 ^ d / 2 ^ e = ((m * 2 ^ (d - e).toNat : ℤ) : K) := by
    rw [mul_div_assoc, ← zpow_sub₀ two_ne_zero]
    push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  rw [round, ← he, hk, roundInt_intCast]
  push_cast
  rw [mul_assoc, ← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_add₀ two_ne_zero,
    sub_add_cancel]

-- In the mode to nearest, rounding in a bounded format is `fl` wherever the last place of `x`
-- is at least `2 ^ qmin`, in particular from the smallest normal number on.
omit [IsStrictOrderedRing K] in
theorem round_nearestEven_eq_fl {p : ℕ} {qmin : ℤ} {x : K} (h : qmin ≤ ulpExp p x) :
    nearestEven.round p qmin x = fl p x := by
  simp [round, roundInt, fl, max_eq_left h]

end RoundingMode

section Format

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K] in
theorem isFloatIn_neg {p : ℕ} {qmin qmax : ℤ} {x : K} (h : IsFloatIn p qmin qmax x) :
    IsFloatIn p qmin qmax (-x) := by
  obtain ⟨m, e, hm, h₁, h₂, rfl⟩ := h
  exact ⟨-m, e, by rwa [abs_neg], h₁, h₂, by push_cast; ring⟩

omit [IsStrictOrderedRing K] [FloorRing K] in
theorem isFloatIn_abs {p : ℕ} {qmin qmax : ℤ} {x : K} (h : IsFloatIn p qmin qmax x) :
    IsFloatIn p qmin qmax |x| := by
  rcases abs_choice x with h' | h' <;> rw [h']
  · exact h
  · exact isFloatIn_neg h

-- An integer multiple `k 2^e` of `2 ^ e`, with `qmin ≤ e` and `|k| ≤ 2 ^ p`, that is at most the
-- largest finite number in absolute value is a number of the format.
theorem isFloatIn_of_abs_le {p : ℕ} {qmin qmax e k : ℤ} (hp : 1 ≤ p) (hq : qmin ≤ qmax)
    (he : qmin ≤ e) (hk : |k| ≤ 2 ^ p) (hle : |(k : K) * 2 ^ e| ≤ (2 ^ p - 1) * 2 ^ qmax) :
    IsFloatIn p qmin qmax ((k : K) * 2 ^ e) := by
  have hpos := two_zpow_pos (K := K) e
  have hqpos := two_zpow_pos (K := K) qmax
  rw [abs_mul, abs_of_pos hpos] at hle
  rcases le_or_gt e qmax with heq | heq
  · rcases hk.lt_or_eq with hlt | hk'
    · exact ⟨k, e, hlt, he, heq, rfl⟩
    -- `k = ± 2^p`: the number is `± 2^(p-1) 2^(e+1)`, and `e < qmax`
    have hkK : |(k : K)| = 2 ^ p := by exact_mod_cast hk'
    have he' : e + 1 ≤ qmax := by
      by_contra hc
      have hcq : e = qmax := by omega
      rw [hkK, hcq] at hle
      linarith
    have h2 : (2 : ℤ) ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ', Nat.sub_add_cancel hp]
    have hlt : |(2 : ℤ) ^ (p - 1)| < 2 ^ p := by
      rw [abs_of_pos (by positivity), h2]
      have : (0 : ℤ) < 2 ^ (p - 1) := by positivity
      omega
    rcases abs_eq (by positivity) |>.1 hk' with h | h
    · refine ⟨2 ^ (p - 1), e + 1, hlt, by omega, he', ?_⟩
      rw [h, zpow_add_one₀ two_ne_zero]
      push_cast [h2]
      ring
    · refine ⟨-2 ^ (p - 1), e + 1, by rwa [abs_neg], by omega, he', ?_⟩
      rw [h, zpow_add_one₀ two_ne_zero]
      push_cast [h2]
      ring
  · -- `e > qmax`: the number is `(k 2^(e - qmax)) 2^qmax`, with a significand below `2^p`
    have hsplit : (2 : K) ^ e = 2 ^ (e - qmax).toNat * 2 ^ qmax := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_add₀ two_ne_zero,
        sub_add_cancel]
    refine ⟨k * 2 ^ (e - qmax).toNat, qmax, ?_, hq, le_rfl, ?_⟩
    · have hK : |(k : K)| * 2 ^ (e - qmax).toNat ≤ 2 ^ p - 1 := by
        rw [hsplit, ← mul_assoc] at hle
        exact le_of_mul_le_mul_right hle hqpos
      have : |k * 2 ^ (e - qmax).toNat| ≤ 2 ^ p - 1 := by
        rw [abs_mul, abs_pow, abs_two]
        exact_mod_cast hK
      omega
    · push_cast
      rw [hsplit, mul_assoc]

-- A rounded number at most the largest finite number in absolute value is a number of the
-- format.
theorem RoundingMode.isFloatIn_round (r : RoundingMode) {p : ℕ} {qmin qmax : ℤ} {x : K}
    (hp : 1 ≤ p) (hq : qmin ≤ qmax) (h : |r.round p qmin x| ≤ (2 ^ p - 1) * 2 ^ qmax) :
    IsFloatIn p qmin qmax (r.round p qmin x) := by
  refine isFloatIn_of_abs_le hp hq (le_max_right _ _) (r.abs_roundInt_le ?_) h
  push_cast
  exact (RoundingMode.abs_div_two_zpow_lt (le_max_left _ _)).le

end Format

namespace BinaryFormat

variable (F : BinaryFormat)

theorem isFloatIn_zero : IsFloatIn F.prec F.qmin F.qmax (0 : ℝ) :=
  ⟨0, F.qmin, by simp, le_rfl, F.qmin_le_qmax, by simp⟩

/-- **Largest finite number.** For a binary format with precision $p$ and greatest last-place
exponent $q_{\max}$, this is the real number $M = (2^p - 1) \cdot 2^{q_{\max}}$. It is the largest
finite number of the format: $M$ is a number of the format (`isFloatIn_maxFinite`) and bounds the
absolute value of every number of the format (`abs_le_maxFinite`). -/
noncomputable def maxFinite : ℝ := (2 ^ F.prec - 1) * 2 ^ F.qmax

theorem maxFinite_pos : 0 < F.maxFinite := by
  have : (2 : ℝ) ≤ 2 ^ F.prec := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ F.prec := pow_le_pow_right₀ (by norm_num) F.one_le_prec
  exact mul_pos (by linarith) (two_zpow_pos _)

theorem isFloatIn_maxFinite : IsFloatIn F.prec F.qmin F.qmax F.maxFinite := by
  have h : (2 : ℤ) ≤ 2 ^ F.prec := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ F.prec := pow_le_pow_right₀ (by norm_num) F.one_le_prec
  refine ⟨2 ^ F.prec - 1, F.qmax, ?_, F.qmin_le_qmax, le_rfl, by rw [maxFinite]; push_cast; ring⟩
  rw [abs_of_pos (by omega)]
  omega

theorem abs_le_maxFinite {x : ℝ} (h : IsFloatIn F.prec F.qmin F.qmax x) : |x| ≤ F.maxFinite := by
  obtain ⟨m, e, hm, -, he, rfl⟩ := h
  have h1 : (1 : ℤ) ≤ 2 ^ F.prec := one_le_pow₀ (by norm_num)
  have hm' : |(m : ℝ)| ≤ 2 ^ F.prec - 1 := by
    have : |m| ≤ 2 ^ F.prec - 1 := by omega
    exact_mod_cast this
  have h0 : (0 : ℝ) ≤ 2 ^ F.prec - 1 := by
    have : (1 : ℝ) ≤ 2 ^ F.prec := by exact_mod_cast h1
    linarith
  rw [maxFinite, abs_mul, abs_of_pos (two_zpow_pos (K := ℝ) e)]
  calc |(m : ℝ)| * 2 ^ e ≤ (2 ^ F.prec - 1) * 2 ^ e :=
        mul_le_mul_of_nonneg_right hm' (two_zpow_pos e).le
    _ ≤ (2 ^ F.prec - 1) * 2 ^ F.qmax :=
        mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) he) h0

end BinaryFormat

/-! ## Values and flags -/

/-- **IEEE values of a binary format.** The values of a binary format $F$ are a single quiet NaN
(the model is canonical-NaN: NaN carries neither a sign nor a payload, and there is no signalling
NaN), the infinities $+\infty$ and $-\infty$, and the finite numbers $\pm m$, given by a sign bit
and a magnitude $m \ge 0$ that is a number of the format. A sign bit `true` means negative, so the
format has the two zeros $+0$ and $-0$.

Source: IEEE Std 754-2019; Goldberg, *What every computer scientist should know about floating-point
arithmetic*, ACM Computing Surveys 23(1), 1991, Section 2.2; Boldo, Jourdan, Leroy and Melquiond,
*Verified compilation of floating-point computations*, Journal of Automated Reasoning 54(2), 2015,
Section 5.1. -/
inductive Value (F : BinaryFormat) where
  /-- The canonical NaN. -/
  | nan
  /-- The infinity of sign bit `neg`: `inf false` is $+\infty$ and `inf true` is $-\infty$. -/
  | inf (neg : Bool)
  /-- The finite number $-m$ if `neg` and $m$ otherwise; `finite true 0` is $-0$. -/
  | finite (neg : Bool) (m : ℝ) (nonneg : 0 ≤ m) (mem : IsFloatIn F.prec F.qmin F.qmax m)

/-- **IEEE status flags.** The five exception flags of IEEE 754 an operation can raise: invalid
operation, division by zero, overflow, underflow and inexact. Each operation returns the flags it
raises. In IEEE 754 the status flags are sticky: once raised, a flag stays raised until it is
cleared.

Source: IEEE Std 754-2019; Goldberg, *What every computer scientist should know about floating-point
arithmetic*, ACM Computing Surveys 23(1), 1991, Section 2.3. -/
structure Flags where
  /-- Invalid operation. -/
  invalid : Bool := false
  /-- Division by zero. -/
  divByZero : Bool := false
  /-- Overflow. -/
  overflow : Bool := false
  /-- Underflow. -/
  underflow : Bool := false
  /-- Inexact. -/
  inexact : Bool := false
  deriving DecidableEq

/-- **Rounding an exact result.** Let $F$ be a binary format with precision $p$ and exponent range
$[q_{\min}, q_{\max}]$, $r$ a rounding mode, $x$ a real number, the exact result of an operation
on finite operands, and $z$ the sign bit the operation gives an exact zero result. The value it
delivers, with the flags it raises, is:

* if $x = 0$, the zero of sign bit $z$, with no flag;
* otherwise let $y$ be $x$ rounded in mode $r$ in the bounded format (with gradual underflow and no
  upper bound on the exponent). If $|y|$ exceeds the largest finite number
  $(2^p - 1) \cdot 2^{q_{\max}}$, the result overflows: it is $\pm\infty$ in the mode to nearest,
  $\pm(2^p - 1) \cdot 2^{q_{\max}}$ toward zero, $+\infty$ or $-(2^p - 1) \cdot 2^{q_{\max}}$
  toward $+\infty$, and $+(2^p - 1) \cdot 2^{q_{\max}}$ or $-\infty$ toward $-\infty$, with the sign
  of $x$, and it raises the overflow and inexact flags;
* otherwise it is the number $y$ of the format, a zero $y$ taking the sign of $x$. It raises the
  inexact flag if $y \ne x$, and the underflow flag if moreover $x$ is tiny,
  $|x| < 2^{q_{\min} + p - 1}$: tininess is detected before rounding, and an exact tiny result
  raises no flag.

Source: IEEE Std 754-2019; Goldberg, *What every computer scientist should know about floating-point
arithmetic*, ACM Computing Surveys 23(1), 1991, Section 2.3.2 (overflow by rounding mode); Boldo,
Jourdan, Leroy and Melquiond, *Verified compilation of floating-point computations*, Journal of
Automated Reasoning 54(2), 2015, Section 5.2. -/
noncomputable def roundResult (F : BinaryFormat) (r : RoundingMode) (x : ℝ) (z : Bool) :
    Value F × Flags :=
  if x = 0 then (.finite z 0 le_rfl F.isFloatIn_zero, {})
  else if h : F.maxFinite < |r.round F.prec F.qmin x| then
    (overflow (decide (x < 0)), { overflow := true, inexact := true })
  else
    (.finite
      (if r.round F.prec F.qmin x = 0 then decide (x < 0) else decide (r.round F.prec F.qmin x < 0))
      |r.round F.prec F.qmin x| (abs_nonneg _)
      (isFloatIn_abs (r.isFloatIn_round F.one_le_prec F.qmin_le_qmax (not_lt.1 h))),
      { underflow := decide (r.round F.prec F.qmin x ≠ x ∧
          |x| < 2 ^ (F.qmin + ((F.prec : ℤ) - 1)))
        inexact := decide (r.round F.prec F.qmin x ≠ x) })
where
  /-- The value an overflow of sign bit `neg` delivers in mode `r`. -/
  overflow (neg : Bool) : Value F :=
    match r, neg with
    | .nearestEven, s => .inf s
    | .towardZero, s => .finite s _ F.maxFinite_pos.le F.isFloatIn_maxFinite
    | .towardPositive, false => .inf false
    | .towardPositive, true => .finite true _ F.maxFinite_pos.le F.isFloatIn_maxFinite
    | .towardNegative, false => .finite false _ F.maxFinite_pos.le F.isFloatIn_maxFinite
    | .towardNegative, true => .inf true

theorem roundResult_zero (F : BinaryFormat) (r : RoundingMode) (z : Bool) :
    roundResult F r 0 z = (.finite z 0 le_rfl F.isFloatIn_zero, {}) := by
  simp [roundResult]

theorem roundResult_of_lt (F : BinaryFormat) (r : RoundingMode) (z : Bool) {x : ℝ} (hx : x ≠ 0)
    (h : F.maxFinite < |r.round F.prec F.qmin x|) :
    roundResult F r x z =
      (roundResult.overflow F r (decide (x < 0)), { overflow := true, inexact := true }) := by
  simp [roundResult, hx, h]

-- A nonzero result that rounds to itself and is at most the largest finite number is delivered
-- exactly, with no flag.
theorem roundResult_of_round_eq (F : BinaryFormat) (r : RoundingMode) (z : Bool) {x : ℝ}
    (hx : x ≠ 0) (hr : r.round F.prec F.qmin x = x) (h : |x| ≤ F.maxFinite)
    (hf : IsFloatIn F.prec F.qmin F.qmax |x|) :
    roundResult F r x z = (.finite (decide (x < 0)) |x| (abs_nonneg x) hf, {}) := by
  simp [roundResult, hx, hr, not_lt.2 h]

/-! ## Operations -/

/-- **Basic operations.** The basic arithmetic operations of IEEE 754 applied to values of a
binary format $F$: the sum, difference, product and quotient of two values, and the square root of
one.

Source: IEEE Std 754-2019. -/
inductive Operation (F : BinaryFormat) where
  /-- The sum $a + b$. -/
  | add (a b : Value F)
  /-- The difference $a - b$. -/
  | sub (a b : Value F)
  /-- The product $a \times b$. -/
  | mul (a b : Value F)
  /-- The quotient $a / b$. -/
  | div (a b : Value F)
  /-- The square root $\sqrt{a}$. -/
  | sqrt (a : Value F)

/-- **Total IEEE-style operation semantics with special values and exceptions.** Let $F$ be a
binary format with values NaN (canonical), $\pm\infty$ and the finite numbers with signed zeros,
and let $r$ be a rounding mode. Each basic operation is total: it returns a value and the flags it
raises.

* An operation with a NaN operand gives NaN and raises no flag.
* The invalid operations give NaN and raise the invalid flag: $(+\infty) + (-\infty)$ and
  $(-\infty) + (+\infty)$, $(+\infty) - (+\infty)$ and $(-\infty) - (-\infty)$, $0 \times \pm\infty$
  and $\pm\infty \times 0$, $0 / 0$, $\pm\infty / \pm\infty$ (for zeros and infinities of either
  sign), and $\sqrt{x}$ for $x < 0$, $-\infty$ included.
* A nonzero finite number divided by a zero gives an infinity whose sign is the exclusive or of the
  operands' signs, and raises the division-by-zero flag.
* The other operations with an infinite operand are exact and raise no flag: a sum with an
  infinite operand is that infinity; a product with an infinite operand and no zero operand, and
  a quotient of an infinity by a finite number, a zero included, is the infinity whose sign is the
  exclusive or of the operands' signs; a finite number divided by an infinity is the zero of that
  sign; and $\sqrt{+\infty} = +\infty$.
* Otherwise the exact real result $x$ is rounded in mode $r$, with overflow according to the mode,
  gradual underflow and the overflow, underflow and inexact flags, as in `roundResult`. An exact
  zero result has a sign fixed by the operation: a sum of two zeros of the same sign is that zero,
  any other exact zero sum is $+0$, or $-0$ when rounding toward $-\infty$; a product or quotient
  has the exclusive or of the signs; $\sqrt{\pm 0} = \pm 0$.

Subtraction $a - b$ is the addition of $a$ and $b$ with its sign bit flipped, so
$(+\infty) - (-\infty) = +\infty$ and $x - x = +0$ for finite $x$, or $-0$ when rounding toward
$-\infty$.

Source: IEEE Std 754-2019; Goldberg, *What every computer scientist should know about floating-point
arithmetic*, ACM Computing Surveys 23(1), 1991, Sections 2.2 and 2.3. -/
noncomputable def Operation.eval {F : BinaryFormat} (r : RoundingMode) :
    Operation F → Value F × Flags
  | .add a b => sum a b
  | .sub a b => sum a (negate b)
  | .mul a b => prod a b
  | .div a b => quot a b
  | .sqrt a => root a
where
  /-- Negation flips the sign bit; the canonical NaN is its own negation. -/
  negate : Value F → Value F
    | .nan => .nan
    | .inf s => .inf (!s)
    | .finite s m h₀ h => .finite (!s) m h₀ h
  /-- Addition. -/
  sum : Value F → Value F → Value F × Flags
    | .nan, _ => (.nan, {})
    | _, .nan => (.nan, {})
    | .inf s, .inf t => if s = t then (.inf s, {}) else (.nan, { invalid := true })
    | .inf s, .finite .. => (.inf s, {})
    | .finite .., .inf t => (.inf t, {})
    | .finite s x _ _, .finite t y _ _ =>
      roundResult F r ((if s then -x else x) + (if t then -y else y))
        (if s = t then s else decide (r = .towardNegative))
  /-- Multiplication. -/
  prod : Value F → Value F → Value F × Flags
    | .nan, _ => (.nan, {})
    | _, .nan => (.nan, {})
    | .inf s, .inf t => (.inf (s ^^ t), {})
    | .inf s, .finite t y _ _ =>
      if y = 0 then (.nan, { invalid := true }) else (.inf (s ^^ t), {})
    | .finite s x _ _, .inf t =>
      if x = 0 then (.nan, { invalid := true }) else (.inf (s ^^ t), {})
    | .finite s x _ _, .finite t y _ _ =>
      roundResult F r ((if s then -x else x) * (if t then -y else y)) (s ^^ t)
  /-- Division. -/
  quot : Value F → Value F → Value F × Flags
    | .nan, _ => (.nan, {})
    | _, .nan => (.nan, {})
    | .inf _, .inf _ => (.nan, { invalid := true })
    | .inf s, .finite t _ _ _ => (.inf (s ^^ t), {})
    | .finite s _ _ _, .inf t => (.finite (s ^^ t) 0 le_rfl F.isFloatIn_zero, {})
    | .finite s x _ _, .finite t y _ _ =>
      if y = 0 then
        if x = 0 then (.nan, { invalid := true }) else (.inf (s ^^ t), { divByZero := true })
      else roundResult F r ((if s then -x else x) / (if t then -y else y)) (s ^^ t)
  /-- Square root. -/
  root : Value F → Value F × Flags
    | .nan => (.nan, {})
    | .inf false => (.inf false, {})
    | .inf true => (.nan, { invalid := true })
    | .finite s x _ _ =>
      if s = true ∧ x ≠ 0 then (.nan, { invalid := true }) else roundResult F r (Real.sqrt x) s

namespace Operation

variable {F : BinaryFormat}

@[simp] theorem eval_add_finite (r : RoundingMode) (s : Bool) (x : ℝ) (hx₀ : 0 ≤ x)
    (hx : IsFloatIn F.prec F.qmin F.qmax x) (t : Bool) (y : ℝ) (hy₀ : 0 ≤ y)
    (hy : IsFloatIn F.prec F.qmin F.qmax y) :
    (add (.finite s x hx₀ hx) (.finite t y hy₀ hy)).eval r =
      roundResult F r ((if s then -x else x) + (if t then -y else y))
        (if s = t then s else decide (r = .towardNegative)) := rfl

@[simp] theorem eval_mul_finite (r : RoundingMode) (s : Bool) (x : ℝ) (hx₀ : 0 ≤ x)
    (hx : IsFloatIn F.prec F.qmin F.qmax x) (t : Bool) (y : ℝ) (hy₀ : 0 ≤ y)
    (hy : IsFloatIn F.prec F.qmin F.qmax y) :
    (mul (.finite s x hx₀ hx) (.finite t y hy₀ hy)).eval r =
      roundResult F r ((if s then -x else x) * (if t then -y else y)) (s ^^ t) := rfl

end Operation

/-! ## Comparison -/

/-- **Four-outcome comparison.** The comparison of two values of a binary format has four mutually
exclusive outcomes: less (`some .lt`), equal (`some .eq`), greater (`some .gt`) and unordered
(`none`). NaN is unordered with every value, itself included. Any other two values compare as
their values in the extended real line, with $-\infty$ below every finite number and $+\infty$
above, so $+0$ and $-0$ are equal. This is IEEE's quiet comparison, which raises no flag.

Source: IEEE Std 754-2019, Clause 5.11; Goldberg, *What every computer scientist should know about
floating-point arithmetic*, ACM Computing Surveys 23(1), 1991, Section 3.2.2; Boldo, Jourdan, Leroy
and Melquiond, *Verified compilation of floating-point computations*, Journal of Automated Reasoning
54(2), 2015, Section 6.3. -/
protected noncomputable def Value.compare {F : BinaryFormat} (a b : Value F) : Option Ordering :=
  match extended a, extended b with
  | some u, some v => some (compareOfLessAndEq u v)
  | _, _ => none
where
  /-- The extended real value of a value other than NaN. -/
  extended : Value F → Option EReal
    | .nan => none
    | .inf s => some (if s then ⊥ else ⊤)
    | .finite s m _ _ => some ((if s then -m else m : ℝ) : EReal)

/-- `a ≤ b` when `a` compares less than or equal to `b`. -/
noncomputable instance {F : BinaryFormat} : LE (Value F) where
  le a b := a.compare b = some .lt ∨ a.compare b = some .eq

namespace Value

variable {F : BinaryFormat}

@[simp] theorem compare_nan_left (a : Value F) : Value.nan.compare a = none := rfl

@[simp] theorem compare_nan_right (a : Value F) : a.compare .nan = none := by
  cases a <;> rfl

theorem compare_eq_none_iff {a b : Value F} : a.compare b = none ↔ a = .nan ∨ b = .nan := by
  cases a <;> cases b <;> simp [Value.compare, compare.extended]

theorem compare_zero_zero (s t : Bool) (h₀ : (0 : ℝ) ≤ 0)
    (h : IsFloatIn F.prec F.qmin F.qmax (0 : ℝ)) :
    (Value.finite s 0 h₀ h).compare (.finite t 0 h₀ h) = some .eq := by
  simp [Value.compare, compare.extended, compareOfLessAndEq]

end Value

/-! ## Properties -/

/-- **`≤` is not a partial order with NaN.** Let $F$ be a binary format and let $a \le b$ mean that
$a$ compares less than or equal to $b$. Then $\mathrm{NaN} \le \mathrm{NaN}$ fails, so $\le$ is not
reflexive, and hence not a partial order on the values of $F$.

Source: Goldberg, *What every computer scientist should know about floating-point arithmetic*, ACM
Computing Surveys 23(1), 1991, Sections 3.2.2 (NaNs are unordered) and 2.3.1 (comparisons with a NaN
return false). -/
theorem not_le_nan_and_not_isPartialOrder (F : BinaryFormat) :
    ¬ (Value.nan : Value F) ≤ .nan ∧ ¬ IsPartialOrder (Value F) (· ≤ ·) := by
  have h : ¬ (Value.nan : Value F) ≤ .nan := by
    simp [LE.le]
  exact ⟨h, fun hp => h (hp.refl _)⟩

/-- **Addition is commutative.** Let $F$ be a binary format and $r$ a rounding mode. For all values
$a$ and $b$ of $F$, the sums $a + b$ and $b + a$ are the same value and raise the same flags. In
this canonical-NaN model this includes the case of a NaN operand. -/
theorem eval_add_comm {F : BinaryFormat} (r : RoundingMode) (a b : Value F) :
    (Operation.add a b).eval r = (Operation.add b a).eval r := by
  cases a <;> cases b <;> simp only [Operation.eval, Operation.eval.sum]
  case inf.inf s t =>
    by_cases h : s = t
    · subst h; rfl
    · simp [h, Ne.symm h]
  case finite.finite s x _ _ t y _ _ =>
    rw [add_comm]
    by_cases h : s = t
    · subst h; rfl
    · simp [h, Ne.symm h]

/-- **Multiplication is commutative.** Let $F$ be a binary format and $r$ a rounding mode. For all
values $a$ and $b$ of $F$, the products $a \times b$ and $b \times a$ are the same value and raise
the same flags. In this canonical-NaN model this includes the case of a NaN operand. -/
theorem eval_mul_comm {F : BinaryFormat} (r : RoundingMode) (a b : Value F) :
    (Operation.mul a b).eval r = (Operation.mul b a).eval r := by
  cases a <;> cases b <;> simp [Operation.eval, Operation.eval.prod, Bool.xor_comm, mul_comm]

/-- **Addition is not associative.** Let $F$ be a binary format and $r$ a rounding mode. There are
values $a$, $b$ and $c$ of $F$ with $(a + b) + c \ne a + (b + c)$. For instance, with $M$ the
largest finite number, $(M + M) + (-M)$ is $+\infty$ when rounding to nearest or toward $+\infty$
and a zero when rounding toward zero or toward $-\infty$, as $M + M$ overflows, while
$M + (M + (-M)) = M$.

Source: Goldberg, *What every computer scientist should know about floating-point arithmetic*, ACM
Computing Surveys 23(1), 1991, Section 3.2 (Ambiguity; Optimizers). -/
theorem not_add_assoc (F : BinaryFormat) (r : RoundingMode) :
    ¬ ∀ a b c : Value F, ((Operation.add ((Operation.add a b).eval r).1 c).eval r).1 =
      ((Operation.add a ((Operation.add b c).eval r).1).eval r).1 := by
  intro hassoc
  obtain ⟨M, hMdef, hM, hMf⟩ : ∃ M : ℝ, M = F.maxFinite ∧ 0 < M ∧
      IsFloatIn F.prec F.qmin F.qmax M :=
    ⟨_, rfl, F.maxFinite_pos, F.isFloatIn_maxFinite⟩
  have hMdef' : M = (2 ^ F.prec - 1) * 2 ^ F.qmax := hMdef
  have hp : |(2 : ℤ) ^ F.prec - 1| < 2 ^ F.prec := by
    have : (1 : ℤ) ≤ 2 ^ F.prec := one_le_pow₀ (by norm_num)
    rw [abs_of_nonneg (by omega)]
    omega
  have hq := F.qmin_le_qmax
  have hrM : r.round F.prec F.qmin M = M := by
    have := r.round_eq_self (K := ℝ) hp hq
    push_cast at this
    rw [hMdef', this]
  have hr2M : r.round F.prec F.qmin (M + M) = M + M := by
    have := r.round_eq_self (K := ℝ) hp (show F.qmin ≤ F.qmax + 1 by omega)
    push_cast at this
    rw [zpow_add_one₀ two_ne_zero] at this
    rw [show M + M = (2 ^ F.prec - 1) * (2 ^ F.qmax * 2) by rw [hMdef']; ring, this]
  have hMM : (Operation.add (.finite false M hM.le hMf) (.finite false M hM.le hMf)).eval r =
      (roundResult.overflow F r false, { overflow := true, inexact := true }) := by
    rw [Operation.eval_add_finite]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [roundResult_of_lt F r _ (by positivity)
      (by rw [← hMdef, hr2M, abs_of_pos (by positivity)]; linarith)]
    simp [not_lt.2 hM.le]
  have hMc : (Operation.add (.finite false M hM.le hMf) (.finite true M hM.le hMf)).eval r =
      (.finite (decide (r = .towardNegative)) 0 le_rfl F.isFloatIn_zero, {}) := by
    simp [roundResult_zero]
  have hM0 (z : Bool) (h₀ : (0 : ℝ) ≤ 0) (h : IsFloatIn F.prec F.qmin F.qmax (0 : ℝ)) :
      (Operation.add (.finite false M hM.le hMf) (.finite z 0 h₀ h)).eval r =
      (.finite false M hM.le hMf, {}) := by
    rw [Operation.eval_add_finite]
    rw [show (if false = true then -M else M) + (if z = true then -0 else 0) = M by simp]
    rw [roundResult_of_round_eq F r _ hM.ne' hrM (by rw [abs_of_pos hM, hMdef])
      (by rw [abs_of_pos hM]; exact hMf)]
    simp [abs_of_pos hM, not_lt.2 hM.le]
  have h := hassoc (.finite false M hM.le hMf) (.finite false M hM.le hMf)
    (.finite true M hM.le hMf)
  rw [hMM, hMc, hM0] at h
  cases r <;>
    simp [roundResult.overflow, Operation.eval, Operation.eval.sum, ← hMdef, roundResult_zero,
      hM.ne] at h

/-- **Multiplication is not associative.** Let $F$ be a binary format with $q_{\min} \le -1$ and
$q_{\max} \ge 1$, as for binary32 and binary64, and let $r$ be a rounding mode. There are values
$a$, $b$ and $c$ of $F$ with $(a \times b) \times c \ne a \times (b \times c)$. For
instance, with $M$ the largest finite number, $(M \times 2) \times \frac{1}{2}$ is $+\infty$ when
rounding to nearest or toward $+\infty$ and $M / 2$ when rounding toward zero or toward
$-\infty$, as $M \times 2$ overflows, while $M \times (2 \times \frac{1}{2}) = M$. -/
theorem not_mul_assoc (F : BinaryFormat) (hmin : F.qmin ≤ -1) (hmax : 1 ≤ F.qmax)
    (r : RoundingMode) :
    ¬ ∀ a b c : Value F, ((Operation.mul ((Operation.mul a b).eval r).1 c).eval r).1 =
      ((Operation.mul a ((Operation.mul b c).eval r).1).eval r).1 := by
  intro hassoc
  obtain ⟨M, hMdef, hM, hMf⟩ : ∃ M : ℝ, M = F.maxFinite ∧ 0 < M ∧
      IsFloatIn F.prec F.qmin F.qmax M :=
    ⟨_, rfl, F.maxFinite_pos, F.isFloatIn_maxFinite⟩
  have hMdef' : M = (2 ^ F.prec - 1) * 2 ^ F.qmax := hMdef
  have hp : |(2 : ℤ) ^ F.prec - 1| < 2 ^ F.prec := by
    have : (1 : ℤ) ≤ 2 ^ F.prec := one_le_pow₀ (by norm_num)
    rw [abs_of_nonneg (by omega)]
    omega
  have hp1 : |(1 : ℤ)| < 2 ^ F.prec := by
    have : (2 : ℤ) ≤ 2 ^ F.prec := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ F.prec := pow_le_pow_right₀ (by norm_num) F.one_le_prec
    rw [abs_one]
    omega
  have hq := F.qmin_le_qmax
  -- `2`, `1/2` and `1` are numbers of the format
  have h2f : IsFloatIn F.prec F.qmin F.qmax (2 : ℝ) := ⟨1, 1, hp1, by omega, hmax, by norm_num⟩
  have hhf : IsFloatIn F.prec F.qmin F.qmax (1 / 2 : ℝ) :=
    ⟨1, -1, hp1, hmin, by omega, by norm_num⟩
  have h1f : IsFloatIn F.prec F.qmin F.qmax (1 : ℝ) := ⟨1, 0, hp1, by omega, by omega, by norm_num⟩
  have hround (m d : ℤ) (hm : |m| < 2 ^ F.prec) (hd : F.qmin ≤ d) :
      r.round F.prec F.qmin ((m : ℝ) * 2 ^ d) = m * 2 ^ d := r.round_eq_self hm hd
  have hr2M : r.round F.prec F.qmin (M * 2) = M * 2 := by
    have := hround (2 ^ F.prec - 1) (F.qmax + 1) hp (by omega)
    push_cast at this
    rw [zpow_add_one₀ two_ne_zero] at this
    rw [hMdef', mul_assoc, this]
  have hrM : r.round F.prec F.qmin M = M := by
    have := hround (2 ^ F.prec - 1) F.qmax hp hq
    push_cast at this
    rw [hMdef', this]
  have hrhM : r.round F.prec F.qmin (M * (1 / 2)) = M * (1 / 2) := by
    have := hround (2 ^ F.prec - 1) (F.qmax - 1) hp (by omega)
    push_cast at this
    rw [zpow_sub_one₀ two_ne_zero] at this
    rw [hMdef', show (2 ^ F.prec - 1) * 2 ^ F.qmax * (1 / 2 : ℝ) =
      (2 ^ F.prec - 1) * (2 ^ F.qmax * 2⁻¹) by ring, this]
  have hr1 : r.round F.prec F.qmin (2 * (1 / 2) : ℝ) = 2 * (1 / 2) := by
    have := hround 1 0 hp1 (by omega)
    norm_num at this ⊢
    exact this
  -- `M × 2` overflows
  have hM2 : (Operation.mul (.finite false M hM.le hMf)
      (.finite false 2 (by norm_num) h2f)).eval r =
      (roundResult.overflow F r false, { overflow := true, inexact := true }) := by
    rw [Operation.eval_mul_finite]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false]
    rw [roundResult_of_lt F r _ (by positivity)
      (by rw [← hMdef, hr2M, abs_of_pos (by positivity)]; linarith)]
    simp [not_lt.2 (by positivity : (0 : ℝ) ≤ M * 2)]
  -- `2 × 1/2 = 1` exactly
  have h21 : (Operation.mul (.finite false 2 (by norm_num) h2f)
      (.finite false (1 / 2) (by norm_num) hhf)).eval r =
      (.finite false 1 zero_le_one h1f, {}) := by
    rw [Operation.eval_mul_finite]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false]
    rw [roundResult_of_round_eq F r _ (by norm_num) hr1 (by
        rw [← hMdef]; norm_num; linarith [show (1 : ℝ) ≤ M from by
          rw [hMdef']
          have h1 : (1 : ℝ) ≤ 2 ^ F.prec - 1 := by
            have : (2 : ℝ) ≤ 2 ^ F.prec := by
              calc (2 : ℝ) = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ F.prec := pow_le_pow_right₀ (by norm_num) F.one_le_prec
            linarith
          have h2 : (1 : ℝ) ≤ 2 ^ F.qmax := one_le_zpow₀ (by norm_num) (by omega)
          nlinarith])
      (by norm_num; exact h1f)]
    norm_num
  -- `M × 1 = M` exactly
  have hM1 : (Operation.mul (.finite false M hM.le hMf) (.finite false 1 zero_le_one h1f)).eval r =
      (.finite false M hM.le hMf, {}) := by
    rw [Operation.eval_mul_finite]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false, mul_one]
    rw [roundResult_of_round_eq F r _ hM.ne' hrM (by rw [abs_of_pos hM, hMdef])
      (by rw [abs_of_pos hM]; exact hMf)]
    simp [abs_of_pos hM, not_lt.2 hM.le]
  -- `M × 1/2 = M / 2` exactly
  have hhMf : IsFloatIn F.prec F.qmin F.qmax (M * (1 / 2)) := by
    rw [hMdef']
    exact ⟨2 ^ F.prec - 1, F.qmax - 1, hp, by omega, by omega, by
      push_cast; rw [zpow_sub_one₀ two_ne_zero]; ring⟩
  have hMh : (Operation.mul (.finite false M hM.le hMf)
      (.finite false (1 / 2) (by norm_num) hhf)).eval r =
      (.finite false |M * (1 / 2)| (abs_nonneg _) (isFloatIn_abs hhMf), {}) := by
    rw [Operation.eval_mul_finite]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false]
    rw [roundResult_of_round_eq F r _ (by positivity) hrhM
      (by rw [abs_of_pos (by positivity), ← hMdef]; linarith) (isFloatIn_abs hhMf)]
    simp [hM.le]
  have h := hassoc (.finite false M hM.le hMf) (.finite false 2 (by norm_num) h2f)
    (.finite false (1 / 2) (by norm_num) hhf)
  rw [hM2, h21, hM1] at h
  cases r
  · simp [roundResult.overflow, Operation.eval, Operation.eval.prod] at h
  · simp [roundResult.overflow, Operation.eval, Operation.eval.prod] at h
  · simp only [roundResult.overflow, ← hMdef, hMh, Value.finite.injEq, true_and] at h
    rw [abs_of_pos (by positivity)] at h
    linarith
  · simp only [roundResult.overflow, ← hMdef, hMh, Value.finite.injEq, true_and] at h
    rw [abs_of_pos (by positivity)] at h
    linarith

end Cslib.Algorithms.Lean.FloatingPoint.IEEE
