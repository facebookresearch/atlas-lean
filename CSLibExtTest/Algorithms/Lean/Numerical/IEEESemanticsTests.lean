/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Numerical.IEEESemantics
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Floor

/-!
# Tests for the total IEEE-style operation semantics

* Rounding in a bounded format, executed over `ℚ` with `decide +kernel`, for `p = 3` and
  `qmin = -4` (smallest normal number `1/4`): the four modes on `±1/3`; gradual underflow of
  `1/64` and a subnormal tie `3/32 ↦ 1/8`, where `fl` (unbounded exponent) keeps `3/32`; and
  agreement with `fl` in the normal range. In any linearly ordered field with a floor, rounding
  toward `-∞` stays below `x`, toward `+∞` above it, and toward zero between `0` and `x ≥ 0`.
* For every format and mode: NaN propagation without flags; each invalid case; division by
  zero; exact operations on infinities; the signed-zero rules (`+0 + -0`, `-0 + -0`, `x - x`,
  `√-0`, products); overflow of `M + M` and `-M + -M` in each mode, `M` the largest finite
  number; and gradual underflow: half the smallest positive number of the format, `2^qmin`,
  rounds to `+0` to nearest and to `2^qmin` toward `+∞`, raising underflow and inexact, while the
  exact tiny result `2^qmin` raises no flag.
* With `p = 3`, `qmin = -4` and `qmax = 0`, the tiny product `(1/2) × (7/16) = 7/32` rounds to
  `1/4`, the smallest normal number, to nearest and toward `+∞`, and raises underflow and inexact,
  as tininess is detected before rounding.
* In binary64, multiplication is not associative.
* Comparison: NaN is unordered with everything, `+0` and `-0` are equal, `-∞ < x < +∞`; `+0 ≤ -0`
  and `-0 ≤ +0` with `+0 ≠ -0`, so `≤` is not antisymmetric even without NaN.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloatingPoint.IEEE

/-! ## Rounding in a bounded format, over `ℚ` -/

-- `1/3 = 5.33… · 2^-4` in the normal range
example : RoundingMode.nearestEven.round 3 (-4) (1 / 3 : ℚ) = 5 / 16 := by decide +kernel
example : RoundingMode.towardPositive.round 3 (-4) (1 / 3 : ℚ) = 3 / 8 := by decide +kernel
example : RoundingMode.towardNegative.round 3 (-4) (1 / 3 : ℚ) = 5 / 16 := by decide +kernel
example : RoundingMode.towardZero.round 3 (-4) (1 / 3 : ℚ) = 5 / 16 := by decide +kernel
example : RoundingMode.nearestEven.round 3 (-4) (-1 / 3 : ℚ) = -5 / 16 := by decide +kernel
example : RoundingMode.towardPositive.round 3 (-4) (-1 / 3 : ℚ) = -5 / 16 := by decide +kernel
example : RoundingMode.towardNegative.round 3 (-4) (-1 / 3 : ℚ) = -3 / 8 := by decide +kernel
example : RoundingMode.towardZero.round 3 (-4) (-1 / 3 : ℚ) = -5 / 16 := by decide +kernel

-- gradual underflow: below `1/4` results are multiples of `2^-4`
example : RoundingMode.nearestEven.round 3 (-4) (1 / 64 : ℚ) = 0 := by decide +kernel
example : RoundingMode.towardPositive.round 3 (-4) (1 / 64 : ℚ) = 1 / 16 := by decide +kernel
example : RoundingMode.towardNegative.round 3 (-4) (-1 / 64 : ℚ) = -1 / 16 := by decide +kernel
example : RoundingMode.towardZero.round 3 (-4) (-1 / 64 : ℚ) = 0 := by decide +kernel
-- a subnormal tie, `3/32 = 1.5 · 2^-4`, goes to the even multiple; `fl` does not round it
example : RoundingMode.nearestEven.round 3 (-4) (3 / 32 : ℚ) = 1 / 8 := by decide +kernel
example : fl 3 (3 / 32 : ℚ) = 3 / 32 := by decide +kernel
-- subnormal numbers are fixed
example : RoundingMode.towardPositive.round 3 (-4) (3 / 16 : ℚ) = 3 / 16 := by decide +kernel
-- in the normal range, rounding to nearest is `fl`
example : RoundingMode.nearestEven.round 3 (-4) (11 / 8 : ℚ) = fl 3 (11 / 8 : ℚ) := by
  decide +kernel
example (x : ℝ) (h : (-4 : ℤ) ≤ ulpExp 3 x) :
    RoundingMode.nearestEven.round 3 (-4) x = fl 3 x :=
  RoundingMode.round_nearestEven_eq_fl h

-- the directed modes round in their direction, in any linearly ordered field with a floor
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K] (p : ℕ)
    (qmin : ℤ) (x : K) : RoundingMode.towardNegative.round p qmin x ≤ x := by
  have hpos := two_zpow_pos (K := K) (max (ulpExp p x) qmin)
  have h := (le_div_iff₀ hpos).1 (Int.floor_le (x / 2 ^ max (ulpExp p x) qmin))
  simpa [RoundingMode.round, RoundingMode.roundInt] using h
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K] (p : ℕ)
    (qmin : ℤ) (x : K) : x ≤ RoundingMode.towardPositive.round p qmin x := by
  have hpos := two_zpow_pos (K := K) (max (ulpExp p x) qmin)
  have h := (div_le_iff₀ hpos).1 (Int.le_ceil (x / 2 ^ max (ulpExp p x) qmin))
  simpa [RoundingMode.round, RoundingMode.roundInt] using h
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K] (p : ℕ)
    (qmin : ℤ) (x : K) (hx : 0 ≤ x) :
    0 ≤ RoundingMode.towardZero.round p qmin x ∧ RoundingMode.towardZero.round p qmin x ≤ x := by
  have hpos := two_zpow_pos (K := K) (max (ulpExp p x) qmin)
  have hm : 0 ≤ x / 2 ^ max (ulpExp p x) qmin := div_nonneg hx hpos.le
  simp only [RoundingMode.round, RoundingMode.roundInt, hm, ↓reduceIte]
  refine ⟨mul_nonneg (by exact_mod_cast Int.floor_nonneg.2 hm) hpos.le, ?_⟩
  exact (le_div_iff₀ hpos).1 (Int.floor_le _)

/-! ## Operations in every format and mode -/

section General

variable {F : BinaryFormat} (r : RoundingMode)

/-- `+0` and `-0`. -/
private noncomputable abbrev zero (F : BinaryFormat) (s : Bool) : Value F :=
  .finite s 0 le_rfl F.isFloatIn_zero

-- NaN propagates and raises no flag
example (a : Value F) : (Operation.add .nan a).eval r = (.nan, {}) := rfl
example (a : Value F) : (Operation.mul a .nan).eval r = (.nan, {}) := by
  cases a <;> rfl
example (a : Value F) : (Operation.div a .nan).eval r = (.nan, {}) := by
  cases a <;> rfl
example : (Operation.sqrt (.nan : Value F)).eval r = (.nan, {}) := rfl

-- the invalid operations
example : (Operation.add (.inf false) (.inf true : Value F)).eval r =
    (.nan, { invalid := true }) := rfl
example : (Operation.add (.inf true) (.inf false : Value F)).eval r =
    (.nan, { invalid := true }) := rfl
example : (Operation.sub (.inf false) (.inf false : Value F)).eval r =
    (.nan, { invalid := true }) := rfl
example : (Operation.sub (.inf true) (.inf true : Value F)).eval r =
    (.nan, { invalid := true }) := rfl
example (s t : Bool) : (Operation.mul (zero F s) (.inf t)).eval r =
    (.nan, { invalid := true }) := by simp [Operation.eval, Operation.eval.prod]
example (s t : Bool) : (Operation.mul (.inf t) (zero F s)).eval r =
    (.nan, { invalid := true }) := by simp [Operation.eval, Operation.eval.prod]
example (s t : Bool) : (Operation.div (zero F s) (zero F t)).eval r =
    (.nan, { invalid := true }) := by simp [Operation.eval, Operation.eval.quot]
example (s t : Bool) : (Operation.div (.inf s) (.inf t : Value F)).eval r =
    (.nan, { invalid := true }) := rfl
example : (Operation.sqrt (.inf true : Value F)).eval r = (.nan, { invalid := true }) := rfl
example (m : ℝ) (h₀ : 0 ≤ m) (h : IsFloatIn F.prec F.qmin F.qmax m) (hm : m ≠ 0) :
    (Operation.sqrt (.finite true m h₀ h)).eval r = (.nan, { invalid := true }) := by
  simp [Operation.eval, Operation.eval.root, hm]

-- division of a nonzero finite number by a zero
example (s t : Bool) (m : ℝ) (h₀ : 0 ≤ m) (h : IsFloatIn F.prec F.qmin F.qmax m) (hm : m ≠ 0) :
    (Operation.div (.finite s m h₀ h) (zero F t)).eval r =
      (.inf (s ^^ t), { divByZero := true }) := by
  simp [Operation.eval, Operation.eval.quot, hm]

-- exact operations on infinities
example (s t : Bool) (m : ℝ) (h₀ : 0 ≤ m) (h : IsFloatIn F.prec F.qmin F.qmax m) :
    (Operation.sub (.inf s) (.finite t m h₀ h)).eval r = (.inf s, {}) := rfl
example : (Operation.sub (.inf false) (.inf true : Value F)).eval r = (.inf false, {}) := rfl
example (s t : Bool) (m : ℝ) (h₀ : 0 ≤ m) (h : IsFloatIn F.prec F.qmin F.qmax m) (hm : m ≠ 0) :
    (Operation.mul (.finite s m h₀ h) (.inf t)).eval r = (.inf (s ^^ t), {}) := by
  simp [Operation.eval, Operation.eval.prod, hm]
example (s t : Bool) : (Operation.div (.inf s) (zero F t)).eval r = (.inf (s ^^ t), {}) := rfl
example (s t : Bool) (m : ℝ) (h₀ : 0 ≤ m) (h : IsFloatIn F.prec F.qmin F.qmax m) :
    (Operation.div (.finite s m h₀ h) (.inf t)).eval r = (zero F (s ^^ t), {}) := rfl
example : (Operation.sqrt (.inf false : Value F)).eval r = (.inf false, {}) := rfl

-- signed zeros
example : (Operation.add (zero F false) (zero F true)).eval .nearestEven = (zero F false, {}) := by
  simp [roundResult_zero]
example : (Operation.add (zero F false) (zero F true)).eval .towardNegative =
    (zero F true, {}) := by
  simp [roundResult_zero]
example : (Operation.add (zero F true) (zero F true)).eval r = (zero F true, {}) := by
  simp [roundResult_zero]
example (m : ℝ) (h₀ : 0 ≤ m) (h : IsFloatIn F.prec F.qmin F.qmax m) :
    (Operation.sub (.finite false m h₀ h) (.finite false m h₀ h)).eval .towardPositive =
      (zero F false, {}) := by
  simp [Operation.eval, Operation.eval.sum, Operation.eval.negate, roundResult_zero]
example (m : ℝ) (h₀ : 0 ≤ m) (h : IsFloatIn F.prec F.qmin F.qmax m) :
    (Operation.sub (.finite false m h₀ h) (.finite false m h₀ h)).eval .towardNegative =
      (zero F true, {}) := by
  simp [Operation.eval, Operation.eval.sum, Operation.eval.negate, roundResult_zero]
example : (Operation.sqrt (zero F true)).eval r = (zero F true, {}) := by
  simp [Operation.eval, Operation.eval.root, roundResult_zero]
example (m : ℝ) (h₀ : 0 ≤ m) (h : IsFloatIn F.prec F.qmin F.qmax m) :
    (Operation.mul (zero F true) (.finite false m h₀ h)).eval r = (zero F true, {}) := by
  simp [roundResult_zero]

/-- The largest finite number `M = (2^p - 1) 2^qmax`, with sign bit `s`. -/
private noncomputable abbrev maxVal (F : BinaryFormat) (s : Bool) : Value F :=
  .finite s _ F.maxFinite_pos.le F.isFloatIn_maxFinite

private theorem round_two_mul_max (F : BinaryFormat) (r : RoundingMode) (s : ℝ)
    (hs : s = 1 ∨ s = -1) :
    r.round F.prec F.qmin (s * F.maxFinite + s * F.maxFinite) =
      s * F.maxFinite + s * F.maxFinite := by
  unfold BinaryFormat.maxFinite
  have h1 : (1 : ℤ) ≤ 2 ^ F.prec := one_le_pow₀ (by norm_num)
  have hq := F.qmin_le_qmax
  rcases hs with rfl | rfl
  · have hp : |(2 : ℤ) ^ F.prec - 1| < 2 ^ F.prec := by rw [abs_of_nonneg (by omega)]; omega
    have := r.round_eq_self (K := ℝ) hp (show F.qmin ≤ F.qmax + 1 by omega)
    push_cast at this
    rw [zpow_add_one₀ two_ne_zero] at this
    convert this using 2 <;> ring
  · have hp : |-((2 : ℤ) ^ F.prec - 1)| < 2 ^ F.prec := by
      rw [abs_neg, abs_of_nonneg (by omega)]; omega
    have := r.round_eq_self (K := ℝ) hp (show F.qmin ≤ F.qmax + 1 by omega)
    push_cast at this
    rw [zpow_add_one₀ two_ne_zero] at this
    convert this using 2 <;> ring

-- overflow of `M + M` in each mode, with the overflow and inexact flags
example (r : RoundingMode) : (Operation.add (maxVal F false) (maxVal F false)).eval r =
    (roundResult.overflow F r false, { overflow := true, inexact := true }) := by
  have hM := F.maxFinite_pos
  have h := round_two_mul_max F r 1 (Or.inl rfl)
  simp only [one_mul] at h
  rw [Operation.eval_add_finite]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [roundResult_of_lt F r _ (by positivity) (by rw [h, abs_of_pos (by positivity)]; linarith)]
  simp [not_lt.2 (by positivity : (0 : ℝ) ≤ _ + _)]
example : roundResult.overflow F .nearestEven false = .inf false := rfl
example : roundResult.overflow F .towardPositive false = .inf false := rfl
example : roundResult.overflow F .towardNegative false = maxVal F false := rfl
example : roundResult.overflow F .towardZero false = maxVal F false := rfl
-- and of `-M + -M`
example (r : RoundingMode) : (Operation.add (maxVal F true) (maxVal F true)).eval r =
    (roundResult.overflow F r true, { overflow := true, inexact := true }) := by
  have hM := F.maxFinite_pos
  have h := round_two_mul_max F r (-1) (Or.inr rfl)
  simp only [neg_one_mul] at h
  rw [Operation.eval_add_finite]
  simp only [↓reduceIte]
  rw [roundResult_of_lt F r _ (by linarith) (by rw [h, abs_of_neg (by linarith)]; linarith)]
  simp [hM]
example : roundResult.overflow F .nearestEven true = .inf true := rfl
example : roundResult.overflow F .towardPositive true = maxVal F true := rfl
example : roundResult.overflow F .towardNegative true = .inf true := rfl
example : roundResult.overflow F .towardZero true = maxVal F true := rfl

-- commutativity, including flags
example (a b : Value F) : (Operation.add a b).eval r = (Operation.add b a).eval r :=
  eval_add_comm r a b
example (a b : Value F) : (Operation.mul a b).eval r = (Operation.mul b a).eval r :=
  eval_mul_comm r a b

-- addition is not associative in every format and mode
example : ¬ ∀ a b c : Value F, ((Operation.add ((Operation.add a b).eval r).1 c).eval r).1 =
    ((Operation.add a ((Operation.add b c).eval r).1).eval r).1 :=
  not_add_assoc F r

-- gradual underflow: half the smallest positive number of the format, `2^qmin`, is tiny and not
-- representable
private theorem log_two_zpow (e : ℤ) : Int.log 2 |(2 : ℝ) ^ e| = e := by
  rw [abs_of_pos (two_zpow_pos e)]
  exact_mod_cast Int.log_zpow (R := ℝ) (b := 2) (by norm_num) e

private theorem abs_one_lt (F : BinaryFormat) : |(1 : ℤ)| < 2 ^ F.prec := by
  rw [abs_one]
  exact one_lt_pow₀ (by norm_num) (by have := F.one_le_prec; omega)

private theorem isFloatIn_min (F : BinaryFormat) :
    IsFloatIn F.prec F.qmin F.qmax ((2 : ℝ) ^ F.qmin) :=
  ⟨1, F.qmin, abs_one_lt F, le_rfl, F.qmin_le_qmax, by simp⟩

-- the smallest positive number of the format is at most the largest finite number, as every
-- number of the format is
private theorem min_le_maxFinite (F : BinaryFormat) : (2 : ℝ) ^ F.qmin ≤ F.maxFinite := by
  simpa [abs_of_pos (two_zpow_pos (K := ℝ) F.qmin)] using F.abs_le_maxFinite (isFloatIn_min F)

private theorem round_half_min (F : BinaryFormat) (r : RoundingMode) :
    r.round F.prec F.qmin ((2 : ℝ) ^ (F.qmin - 1)) =
      (r.roundInt (1 / 2 : ℝ) : ℝ) * 2 ^ F.qmin := by
  have hp := F.one_le_prec
  have he : max (ulpExp F.prec ((2 : ℝ) ^ (F.qmin - 1))) F.qmin = F.qmin := by
    rw [ulpExp, log_two_zpow]
    exact max_eq_right (by omega)
  rw [RoundingMode.round, he, ← zpow_sub₀ two_ne_zero, show F.qmin - 1 - F.qmin = -1 by ring]
  norm_num

private theorem tiny_half_min (F : BinaryFormat) :
    |(2 : ℝ) ^ (F.qmin - 1)| < 2 ^ (F.qmin + ((F.prec : ℤ) - 1)) := by
  have hp := F.one_le_prec
  rw [abs_of_pos (two_zpow_pos _)]
  exact zpow_lt_zpow_right₀ (by norm_num) (by omega)

example (z : Bool) : roundResult F .nearestEven ((2 : ℝ) ^ (F.qmin - 1)) z =
    (zero F false, { underflow := true, inexact := true }) := by
  have hrne : rne (1 / 2 : ℝ) = 0 := by
    have : ⌊(1 / 2 : ℝ)⌋ = 0 := Int.floor_eq_iff.2 (by norm_num)
    unfold rne
    rw [this]
    norm_num
  have h : RoundingMode.nearestEven.round F.prec F.qmin ((2 : ℝ) ^ (F.qmin - 1)) = 0 := by
    rw [round_half_min, RoundingMode.roundInt, hrne, Int.cast_zero, zero_mul]
  have hx := (two_zpow_pos (K := ℝ) (F.qmin - 1)).ne'
  have hp := F.one_le_prec
  unfold roundResult
  split_ifs with h₀ h₁
  · exact absurd h₀ hx
  · rw [h, abs_zero] at h₁
    exact absurd h₁ (not_lt.2 F.maxFinite_pos.le)
  · simp only [h, abs_zero, Prod.mk.injEq]
    refine ⟨by simp [(two_zpow_pos (K := ℝ) (F.qmin - 1)).le], ?_⟩
    simp [hx.symm]
    omega

example (z : Bool) : roundResult F .towardPositive ((2 : ℝ) ^ (F.qmin - 1)) z =
    (.finite false _ (two_zpow_pos F.qmin).le (isFloatIn_min F),
      { underflow := true, inexact := true }) := by
  have hce : ⌈(1 / 2 : ℝ)⌉ = 1 := Int.ceil_eq_iff.2 (by norm_num)
  have h : RoundingMode.towardPositive.round F.prec F.qmin ((2 : ℝ) ^ (F.qmin - 1)) =
      2 ^ F.qmin := by
    rw [round_half_min, RoundingMode.roundInt, hce, Int.cast_one, one_mul]
  have hne : (2 : ℝ) ^ F.qmin ≠ 2 ^ (F.qmin - 1) :=
    (zpow_right_injective₀ (by norm_num) (by norm_num)).ne (by omega)
  have hx := (two_zpow_pos (K := ℝ) (F.qmin - 1)).ne'
  have hpos := two_zpow_pos (K := ℝ) F.qmin
  have hp := F.one_le_prec
  unfold roundResult
  split_ifs with h₀ h₁ h₂
  · exact absurd h₀ hx
  · rw [h, abs_of_pos hpos] at h₁
    exact absurd h₁ (not_lt.2 (min_le_maxFinite F))
  · rw [h] at h₂
    exact absurd h₂ hpos.ne'
  · simp only [h, abs_of_pos hpos, Prod.mk.injEq]
    refine ⟨by simpa using hpos.le, ?_⟩
    simp [hne]
    omega

-- the smallest positive number of the format itself is exact: no flag, although it is tiny
example (r : RoundingMode) (z : Bool) : roundResult F r ((2 : ℝ) ^ F.qmin) z =
    (.finite false _ (two_zpow_pos F.qmin).le (isFloatIn_min F), {}) := by
  have hr : r.round F.prec F.qmin ((2 : ℝ) ^ F.qmin) = 2 ^ F.qmin := by
    have := r.round_eq_self (K := ℝ) (p := F.prec) (qmin := F.qmin) (m := 1) (d := F.qmin)
      (abs_one_lt F) le_rfl
    simpa using this
  have hpos := two_zpow_pos (K := ℝ) F.qmin
  rw [roundResult_of_round_eq F r z hpos.ne' hr (by rw [abs_of_pos hpos]; exact min_le_maxFinite F)
    (by rw [abs_of_pos hpos]; exact isFloatIn_min F)]
  simp [abs_of_pos hpos, not_lt.2 hpos.le]

end General

/-! ## A tiny result that rounds to the smallest normal number -/

/-- The format with `p = 3`, `qmin = -4` and `qmax = 0`, whose smallest normal number is `1/4`. -/
private def fmt3 : BinaryFormat := ⟨3, -4, 0, by norm_num, by norm_num⟩

private theorem half_mem : IsFloatIn fmt3.prec fmt3.qmin fmt3.qmax (1 / 2 : ℝ) :=
  ⟨1, -1, by norm_num [fmt3], by norm_num [fmt3], by norm_num [fmt3], by norm_num⟩

private theorem seven_sixteenths_mem : IsFloatIn fmt3.prec fmt3.qmin fmt3.qmax (7 / 16 : ℝ) :=
  ⟨7, -4, by norm_num [fmt3], by norm_num [fmt3], by norm_num [fmt3], by norm_num⟩

private theorem quarter_mem : IsFloatIn fmt3.prec fmt3.qmin fmt3.qmax (1 / 4 : ℝ) :=
  ⟨1, -2, by norm_num [fmt3], by norm_num [fmt3], by norm_num [fmt3], by norm_num⟩

-- `7/32` is below `1/4`, so it is rounded at the last place `2^-4`, as `7/2 · 2^-4`
private theorem round_seven_thirty_seconds (r : RoundingMode) :
    r.round 3 (-4) (7 / 32 : ℝ) = (r.roundInt (7 / 2 : ℝ) : ℝ) * 2 ^ (-4 : ℤ) := by
  have hlog : Int.log 2 |(7 / 32 : ℝ)| < -1 :=
    (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) (by norm_num)).1 (by norm_num)
  have he : max (ulpExp 3 (7 / 32 : ℝ)) (-4) = -4 :=
    max_eq_right (by unfold ulpExp; push_cast; omega)
  rw [RoundingMode.round, he]
  norm_num

private theorem eval_tiny_product (r : RoundingMode) (hr : r.roundInt (7 / 2 : ℝ) = 4) :
    (Operation.mul (.finite false (1 / 2) (by norm_num) half_mem)
      (.finite false (7 / 16) (by norm_num) seven_sixteenths_mem)).eval r =
      (.finite false (1 / 4) (by norm_num) quarter_mem,
        { underflow := true, inexact := true }) := by
  have hround : r.round fmt3.prec fmt3.qmin ((1 / 2 : ℝ) * (7 / 16)) = 1 / 4 := by
    rw [show (1 / 2 : ℝ) * (7 / 16) = 7 / 32 by norm_num]
    change r.round 3 (-4) (7 / 32 : ℝ) = 1 / 4
    rw [round_seven_thirty_seconds, hr]
    norm_num
  rw [Operation.eval_mul_finite]
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false]
  unfold roundResult
  split_ifs with h₀ h₁ h₂
  · norm_num at h₀
  · rw [hround] at h₁
    norm_num [BinaryFormat.maxFinite, fmt3] at h₁
  · rw [hround] at h₂
    norm_num at h₂
  · simp only [hround, Prod.mk.injEq]
    refine ⟨by norm_num, ?_⟩
    norm_num [fmt3]

-- `7/32 = 3.5 · 2^-4` is a tie between `3 · 2^-4` and `4 · 2^-4 = 1/4`; it goes to the even `4`
example : (Operation.mul (.finite false (1 / 2) (by norm_num) half_mem)
    (.finite false (7 / 16) (by norm_num) seven_sixteenths_mem)).eval .nearestEven =
      (.finite false (1 / 4) (by norm_num) quarter_mem,
        { underflow := true, inexact := true }) := by
  refine eval_tiny_product _ ?_
  have hfl : ⌊(7 / 2 : ℝ)⌋ = 3 := Int.floor_eq_iff.2 (by norm_num)
  simp only [RoundingMode.roundInt, rne, hfl]
  norm_num
  decide

-- toward `+∞` it rounds up to `1/4`
example : (Operation.mul (.finite false (1 / 2) (by norm_num) half_mem)
    (.finite false (7 / 16) (by norm_num) seven_sixteenths_mem)).eval .towardPositive =
      (.finite false (1 / 4) (by norm_num) quarter_mem, { underflow := true, inexact := true }) :=
  eval_tiny_product _ (Int.ceil_eq_iff.2 (by norm_num))

/-! ## binary64 -/

/-- The binary64 format: `p = 53`, `qmin = -1074`, `qmax = 971`. -/
private def binary64 : BinaryFormat := ⟨53, -1074, 971, by norm_num, by norm_num⟩

-- multiplication is not associative in binary64, in every mode
example (r : RoundingMode) :
    ¬ ∀ a b c : Value binary64, ((Operation.mul ((Operation.mul a b).eval r).1 c).eval r).1 =
      ((Operation.mul a ((Operation.mul b c).eval r).1).eval r).1 :=
  not_mul_assoc binary64 (by norm_num [binary64]) (by norm_num [binary64]) r

/-! ## Comparison -/

section Compare

variable {F : BinaryFormat}

example (a : Value F) : Value.nan.compare a = none ∧ a.compare .nan = none := by simp
example (a b : Value F) (h : a.compare b = none) : a = .nan ∨ b = .nan :=
  Value.compare_eq_none_iff.1 h
example : (zero F false).compare (zero F true) = some .eq := Value.compare_zero_zero _ _ _ _
example (m : ℝ) (h₀ : 0 ≤ m) (h : IsFloatIn F.prec F.qmin F.qmax m) :
    (Value.inf true).compare (.finite false m h₀ h) = some .lt ∧
      (Value.finite true m h₀ h).compare (.inf false) = some .lt := by
  simp [Value.compare, Value.compare.extended, compareOfLessAndEq]

-- `+0 ≤ -0` and `-0 ≤ +0` although `+0 ≠ -0`
example : zero F false ≤ zero F true ∧ zero F true ≤ zero F false ∧
    zero F false ≠ zero F true := by
  refine ⟨Or.inr (Value.compare_zero_zero _ _ _ _), Or.inr (Value.compare_zero_zero _ _ _ _), ?_⟩
  simp

-- `NaN ≤ NaN` fails, so `≤` is not a partial order
example : ¬ (Value.nan : Value F) ≤ .nan ∧ ¬ IsPartialOrder (Value F) (· ≤ ·) :=
  not_le_nan_and_not_isPartialOrder F

end Compare

end Cslib.Algorithms.Lean.FloatingPoint.IEEE
