/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

/-!
# Certified numerical analysis

Exact certificates for numerical claims: rational interval enclosures, certified bisection,
quadrature and Taylor truncation bounds, error budgets, and provenance records.

## i. Overview

No floating-point value is a proof object here. A computation may be guided by floating point,
but every numerical claim is checked by exact rational arithmetic or by a named Mathlib inequality.

* A `RatInterval` is a pair of rational endpoints, and `I.Encloses x` states that the real number
  `x` lies between them. Interval operations are computable functions of the endpoints, and their
  soundness is proved separately (`RatInterval.Encloses.add`, `RatInterval.Encloses.sub`, ...).
  Enclosures of `exp q` come from Mathlib's Taylor bound `Real.exp_bound` and enclosures of `√q`
  from exact rational squares. Outward rounding (`RatInterval.Encloses.widen`,
  `RatInterval.Encloses.roundOut`) is proved, not asserted.
* Roots are bracketed by the intermediate value theorem and are unique for strictly monotone
  functions; no differentiability is assumed.
* `bisectRun` runs bisection on rational brackets from a list of sign decisions. When each
  decision is certified by the sign of `f` at its midpoint (`SignCertified`), `n` steps return a
  bracket of width `(b - a) / 2 ^ n` that still contains a root. The real-valued bisection sequence
  `MetaMathlibExt.IsBisectionSequence` of `MathlibExt/Analysis/Calculus/Bisection.lean` and its
  convergence rate are not repeated here. Its invariants concern infinite sequences of reals,
  whereas a certificate needs finitely many steps with rational endpoints, so the corresponding
  invariants of `bisectRun` are proved directly.
* Trapezoidal rule and Taylor truncation errors are bounded from explicit derivative bounds.
* The error-budget lemmas keep the numerical error separate from the measured-data uncertainty.
  The data uncertainty is an input hypothesis, and its effect on the output enters only through an
  explicit conditioning hypothesis; a residual bound alone is never used as an error bound.
* A `CertifiedRoot` records the exact rational computation that encloses the unique root of an
  equation in its initial bracket, together with a `Provenance` of units, data version, tolerance
  and the cited Mathlib lemmas. The capstone `equilibriumCapstone` certifies the root of
  `x + exp x = 2` in `[453/1024, 227/512]`.

## ii. Key results

- `encloses_expInterval` : a computable rational enclosure of `exp q` for rational `|q| ≤ 1`
- `encloses_expOneInterval` : `e ∈ [2718/1000, 2719/1000]`
- `exists_root_of_nonpos_of_nonneg` : a sign change of a continuous function brackets a root
- `existsUnique_root_of_strictMonoOn` : the root is unique for a strictly monotone function
- `bisectRun_width_and_root` : `n` certified bisection steps give width `(b - a) / 2 ^ n` and
  still bracket a root
- `encloses_bisectRun_of_strictMonoOn` : the root of a strictly monotone function lies in every
  certified bracket
- `abs_trapezoidal_error_le` : the trapezoidal rule error bound from a second-derivative bound on
  the interval
- `abs_sub_taylorWithinEval_le` : the Taylor truncation bound with the Lagrange constant
- `abs_sub_le_numerical_add_data` : numerical error plus conditioned data uncertainty
- `abs_sub_root_le_of_residual` : a residual bound gives an error bound through conditioning
- `equilibriumCapstone` : the certified root of `x + exp x = 2` with its provenance record, in
  the bracket `[453/1024, 227/512]` (`equilibriumCapstone_enclosure`)

## iii. Table of contents

- A. Rational interval certificates
- B. Root bracketing and uniqueness
- C. Certified bisection
- D. Quadrature and Taylor truncation bounds
- E. Error budgets
- F. Provenance records
- G. Capstone: `x + exp x = 2`

## iv. References

- R. L. Burden and J. D. Faires, *Numerical Analysis*, 10th ed., Cengage Learning, 2016,
  Sections 1.1, 2.1 and 4.4.
- W. Tucker, *Validated Numerics: A Short Introduction to Rigorous Computations*, Princeton
  University Press, 2011.
- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002, Chapter 1.
-/

@[expose] public section

namespace MathlibExt.Analysis.Numerical.Certified

/-! ## A. Rational interval certificates -/

/-- A closed interval `[lower, upper]` with rational endpoints. -/
structure RatInterval where
  /-- The lower endpoint. -/
  lower : ℚ
  /-- The upper endpoint. -/
  upper : ℚ

namespace RatInterval

/-- The width `upper - lower` of an interval. -/
def width (I : RatInterval) : ℚ :=
  I.upper - I.lower

/-- The midpoint of an interval. -/
def mid (I : RatInterval) : ℚ :=
  (I.lower + I.upper) / 2

/-- `I.Encloses x`: the real number `x` lies in the rational interval `I`. -/
def Encloses (I : RatInterval) (x : ℝ) : Prop :=
  x ∈ Set.Icc (I.lower : ℝ) I.upper

/-- The degenerate interval `[q, q]`. -/
@[simps]
def ofRat (q : ℚ) : RatInterval :=
  ⟨q, q⟩

/-- The interval `[q - ε, q + ε]`. -/
@[simps]
def ofCenter (q ε : ℚ) : RatInterval :=
  ⟨q - ε, q + ε⟩

/-- Interval addition. -/
@[simps]
def add (I J : RatInterval) : RatInterval :=
  ⟨I.lower + J.lower, I.upper + J.upper⟩

/-- Interval negation. -/
@[simps]
def neg (I : RatInterval) : RatInterval :=
  ⟨-I.upper, -I.lower⟩

/-- Interval subtraction. -/
@[simps]
def sub (I J : RatInterval) : RatInterval :=
  ⟨I.lower - J.upper, I.upper - J.lower⟩

/-- Outward rounding of the endpoints to the grid `10⁻ᵏ`: the lower endpoint is rounded down and
the upper endpoint up. -/
@[simps]
def roundOut (I : RatInterval) (k : ℕ) : RatInterval :=
  ⟨⌊I.lower * 10 ^ k⌋ / 10 ^ k, ⌈I.upper * 10 ^ k⌉ / 10 ^ k⟩

/-- `I.Encloses x` unfolds to the two endpoint inequalities. -/
lemma encloses_iff {I : RatInterval} {x : ℝ} :
    I.Encloses x ↔ (I.lower : ℝ) ≤ x ∧ x ≤ I.upper :=
  Iff.rfl

/-- An interval that encloses a value has nonnegative width. -/
lemma Encloses.width_nonneg {I : RatInterval} {x : ℝ} (h : I.Encloses x) : 0 ≤ I.width := by
  have h' : (I.lower : ℝ) ≤ I.upper := h.1.trans h.2
  exact sub_nonneg.2 (by exact_mod_cast h')

/-- The midpoint approximates an enclosed value to within half of the width. -/
lemma Encloses.abs_sub_mid_le {I : RatInterval} {x : ℝ} (h : I.Encloses x) :
    |x - I.mid| ≤ (I.width : ℝ) / 2 := by
  obtain ⟨h₁, h₂⟩ := h
  simp only [mid, width, Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_ofNat]
  rw [abs_le]
  constructor <;> linarith

/-- The degenerate interval `[q, q]` encloses `q`. -/
lemma encloses_ofRat (q : ℚ) : (ofRat q).Encloses q :=
  ⟨le_rfl, le_rfl⟩

/-- A rational approximation `q` of `x` with a proved error bound `ε` gives the enclosure
`[q - ε, q + ε]`. -/
lemma encloses_ofCenter {x : ℝ} {q ε : ℚ} (h : |x - q| ≤ ε) : (ofCenter q ε).Encloses x := by
  obtain ⟨h₁, h₂⟩ := abs_le.1 h
  rw [encloses_iff, ofCenter_lower, ofCenter_upper]
  push_cast
  constructor <;> linarith

/-- Proved outward rounding: moving the endpoints outward keeps an enclosure. -/
lemma Encloses.widen {I J : RatInterval} {x : ℝ} (h : I.Encloses x) (hl : J.lower ≤ I.lower)
    (hu : I.upper ≤ J.upper) : J.Encloses x :=
  ⟨(Rat.cast_le.2 hl).trans h.1, h.2.trans (Rat.cast_le.2 hu)⟩

/-- Rounding the endpoints outward to the grid `10⁻ᵏ` keeps an enclosure. -/
lemma Encloses.roundOut {I : RatInterval} {x : ℝ} (h : I.Encloses x) (k : ℕ) :
    (I.roundOut k).Encloses x := by
  have hk : (0 : ℚ) < 10 ^ k := by positivity
  refine h.widen ?_ ?_
  · rw [roundOut_lower, div_le_iff₀ hk]
    exact Int.floor_le _
  · rw [roundOut_upper, le_div_iff₀ hk]
    exact Int.le_ceil _

/-- Outward rounding to the grid `10⁻ᵏ` widens an interval by at most `2 / 10 ^ k`. -/
lemma width_roundOut_le (I : RatInterval) (k : ℕ) :
    (I.roundOut k).width ≤ I.width + 2 / 10 ^ k := by
  have hk : (0 : ℚ) < 10 ^ k := by positivity
  have h₁ : I.lower * 10 ^ k - 1 < ⌊I.lower * 10 ^ k⌋ := Int.sub_one_lt_floor _
  have h₂ : (⌈I.upper * 10 ^ k⌉ : ℚ) < I.upper * 10 ^ k + 1 := Int.ceil_lt_add_one _
  rw [← mul_le_mul_iff_left₀ hk]
  simp only [width, roundOut_lower, roundOut_upper, sub_mul, add_mul,
    div_mul_cancel₀ _ hk.ne']
  linarith

/-- Interval addition is sound. -/
lemma Encloses.add {I J : RatInterval} {x y : ℝ} (hx : I.Encloses x) (hy : J.Encloses y) :
    (I.add J).Encloses (x + y) := by
  rw [encloses_iff, add_lower, add_upper]
  push_cast
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

/-- Interval negation is sound. -/
lemma Encloses.neg {I : RatInterval} {x : ℝ} (h : I.Encloses x) : I.neg.Encloses (-x) := by
  rw [encloses_iff, neg_lower, neg_upper]
  push_cast
  exact ⟨neg_le_neg h.2, neg_le_neg h.1⟩

/-- Interval subtraction is sound. -/
lemma Encloses.sub {I J : RatInterval} {x y : ℝ} (hx : I.Encloses x) (hy : J.Encloses y) :
    (I.sub J).Encloses (x - y) := by
  rw [encloses_iff, sub_lower, sub_upper]
  push_cast
  exact ⟨sub_le_sub hx.1 hy.2, sub_le_sub hx.2 hy.1⟩

/-- A nonnegative lower endpoint certifies `0 ≤ x`. -/
lemma Encloses.nonneg {I : RatInterval} {x : ℝ} (h : I.Encloses x) (hl : 0 ≤ I.lower) : 0 ≤ x :=
  (Rat.cast_nonneg.2 hl).trans h.1

/-- A nonpositive upper endpoint certifies `x ≤ 0`. -/
lemma Encloses.nonpos {I : RatInterval} {x : ℝ} (h : I.Encloses x) (hu : I.upper ≤ 0) : x ≤ 0 :=
  h.2.trans (Rat.cast_nonpos.2 hu)

end RatInterval

/-- The Taylor partial sum `∑ k < n, q ^ k / k!` of `exp` at a rational point. -/
def expPartialSum (q : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, q ^ k / k.factorial

/-- The rational remainder bound `|q| ^ n * ((n + 1) / (n! * n))` of Mathlib's `Real.exp_bound`,
valid for `|q| ≤ 1` and `0 < n`; for `n = 0` the formula divides by zero and evaluates to `0`. -/
def expRemainderBound (q : ℚ) (n : ℕ) : ℚ :=
  |q| ^ n * ((n + 1) / (n.factorial * n))

/-- Mathlib's Taylor bound `Real.exp_bound` at a rational point, with rational partial sum and
remainder bound. -/
lemma abs_exp_sub_expPartialSum_le {q : ℚ} (hq : |q| ≤ 1) {n : ℕ} (hn : 0 < n) :
    |Real.exp q - expPartialSum q n| ≤ expRemainderBound q n := by
  have h := Real.exp_bound (x := (q : ℝ)) (by exact_mod_cast hq) hn
  simp only [expPartialSum, expRemainderBound]
  push_cast at h ⊢
  exact h

/-- The rational interval `expPartialSum q n ± expRemainderBound q n`. It encloses `exp q` when
`|q| ≤ 1` and `0 < n` (`encloses_expInterval`); outside that range it need not. -/
def expInterval (q : ℚ) (n : ℕ) : RatInterval :=
  RatInterval.ofCenter (expPartialSum q n) (expRemainderBound q n)

/-- `expInterval q n` encloses `exp q` for rational `|q| ≤ 1` and `0 < n`. -/
lemma encloses_expInterval {q : ℚ} (hq : |q| ≤ 1) {n : ℕ} (hn : 0 < n) :
    (expInterval q n).Encloses (Real.exp q) :=
  RatInterval.encloses_ofCenter (abs_exp_sub_expPartialSum_le hq hn)

/-- The width of `expInterval q n` is twice the remainder bound. -/
lemma expInterval_width (q : ℚ) (n : ℕ) :
    (expInterval q n).width = 2 * expRemainderBound q n := by
  simp only [expInterval, RatInterval.width, RatInterval.ofCenter_lower,
    RatInterval.ofCenter_upper]
  ring

/-- The certified three-decimal interval for `e`: the eight-term Taylor enclosure of `exp 1`,
rounded outward to the grid `10⁻³`. It equals `[2718/1000, 2719/1000]`
(`expOneInterval_eq`). -/
def expOneInterval : RatInterval :=
  (expInterval 1 8).roundOut 3

/-- The endpoints of `expOneInterval`, computed by exact rational arithmetic. -/
lemma expOneInterval_eq : expOneInterval = ⟨2718 / 1000, 2719 / 1000⟩ := by
  norm_num [expOneInterval, expInterval, expPartialSum, expRemainderBound, Finset.sum_range_succ,
    Nat.factorial, RatInterval.roundOut]

/-- `e ∈ [2718/1000, 2719/1000]`, an enclosure of width `1/1000`. -/
lemma encloses_expOneInterval : expOneInterval.Encloses (Real.exp 1) := by
  have h := (encloses_expInterval (q := 1) (by norm_num) (n := 8) (by norm_num)).roundOut 3
  rwa [Rat.cast_one] at h

/-- The rational interval `[a, b]` encloses `√q` when `0 ≤ b` and `a ^ 2 ≤ q ≤ b ^ 2`. -/
lemma encloses_sqrt {q a b : ℚ} (hb : 0 ≤ b) (hlower : a ^ 2 ≤ q) (hupper : q ≤ b ^ 2) :
    (⟨a, b⟩ : RatInterval).Encloses (Real.sqrt q) := by
  refine ⟨(le_abs_self (a : ℝ)).trans (Real.abs_le_sqrt (by exact_mod_cast hlower)), ?_⟩
  change Real.sqrt q ≤ b
  rw [Real.sqrt_le_left (by exact_mod_cast hb)]
  exact_mod_cast hupper

/-! ## B. Root bracketing and uniqueness -/

/-- **Root bracketing.** A function continuous on `[a, b]` with `f a ≤ 0 ≤ f b` has a root in
`[a, b]`, by the intermediate value theorem. -/
lemma exists_root_of_nonpos_of_nonneg {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : f a ≤ 0) (hb : 0 ≤ f b) :
    ∃ c ∈ Set.Icc a b, f c = 0 :=
  intermediate_value_Icc hab hf ⟨ha, hb⟩

/-- **Root bracketing**, sign-flipped case: a function continuous on `[a, b]` with
`0 ≤ f a` and `f b ≤ 0` has a root in `[a, b]`. -/
lemma exists_root_of_nonneg_of_nonpos {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : 0 ≤ f a) (hb : f b ≤ 0) :
    ∃ c ∈ Set.Icc a b, f c = 0 :=
  intermediate_value_Icc' hab hf ⟨hb, ha⟩

/-- **Root uniqueness.** A function strictly monotone on `s` has at most one root in `s`. -/
lemma root_unique_of_strictMonoOn {f : ℝ → ℝ} {s : Set ℝ} (hf : StrictMonoOn f s) {x y : ℝ}
    (hx : x ∈ s) (hy : y ∈ s) (hfx : f x = 0) (hfy : f y = 0) : x = y :=
  hf.injOn hx hy (hfx.trans hfy.symm)

/-- A function continuous and strictly monotone on `[a, b]` with `f a ≤ 0 ≤ f b` has exactly
one root in `[a, b]`. -/
lemma existsUnique_root_of_strictMonoOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hmono : StrictMonoOn f (Set.Icc a b))
    (ha : f a ≤ 0) (hb : 0 ≤ f b) : ∃! c, c ∈ Set.Icc a b ∧ f c = 0 := by
  obtain ⟨c, hc, hfc⟩ := exists_root_of_nonpos_of_nonneg hab hf ha hb
  exact ⟨c, ⟨hc, hfc⟩, fun y hy => root_unique_of_strictMonoOn hmono hy.1 hc hy.2 hfc⟩

/-- A function continuous and strictly antitone on `[a, b]` with `0 ≤ f a` and `f b ≤ 0` has
exactly one root in `[a, b]`. -/
lemma existsUnique_root_of_strictAntiOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hanti : StrictAntiOn f (Set.Icc a b))
    (ha : 0 ≤ f a) (hb : f b ≤ 0) : ∃! c, c ∈ Set.Icc a b ∧ f c = 0 := by
  obtain ⟨c, hc, hfc⟩ := exists_root_of_nonneg_of_nonpos hab hf ha hb
  exact ⟨c, ⟨hc, hfc⟩, fun y hy => hanti.injOn hy.1 hc (hy.2.trans hfc.symm)⟩

/-! ## C. Certified bisection -/

/-- One bisection step on the rational bracket `I` with midpoint `m = I.mid`. The decision `true`
records `0 ≤ f m` and keeps `[I.lower, m]`; the decision `false` records `f m ≤ 0` and keeps
`[m, I.upper]`. -/
def bisectStep : Bool → RatInterval → RatInterval
  | true, I => ⟨I.lower, I.mid⟩
  | false, I => ⟨I.mid, I.upper⟩

/-- The `n`-step bisection: the bracket obtained from `I` by applying the `n = ds.length`
decisions `ds` in order. -/
def bisectRun : List Bool → RatInterval → RatInterval
  | [], I => I
  | d :: ds, I => bisectRun ds (bisectStep d I)

/-- `SignCertified f ds I`: each decision of `ds`, applied from `I`, matches the sign of `f` at the
current midpoint (`true` means `0 ≤ f m`, `false` means `f m ≤ 0`). -/
def SignCertified (f : ℝ → ℝ) : List Bool → RatInterval → Prop
  | [], _ => True
  | true :: ds, I => 0 ≤ f I.mid ∧ SignCertified f ds (bisectStep true I)
  | false :: ds, I => f I.mid ≤ 0 ∧ SignCertified f ds (bisectStep false I)

/-- A bisection step halves the width of the bracket. -/
lemma bisectStep_width (d : Bool) (I : RatInterval) : (bisectStep d I).width = I.width / 2 := by
  cases d <;> simp only [bisectStep, RatInterval.width, RatInterval.mid] <;> ring

/-- After `n = ds.length` bisection steps the bracket has width `I.width / 2 ^ n`. -/
lemma bisectRun_width (ds : List Bool) (I : RatInterval) :
    (bisectRun ds I).width = I.width / 2 ^ ds.length := by
  induction ds generalizing I with
  | nil => simp [bisectRun]
  | cons d ds ih =>
    rw [bisectRun, ih, bisectStep_width, List.length_cons, pow_succ]
    ring

/-- A bisection step keeps an ordered bracket ordered and inside the previous bracket. -/
lemma bisectStep_le (d : Bool) {I : RatInterval} (h : I.lower ≤ I.upper) :
    I.lower ≤ (bisectStep d I).lower ∧ (bisectStep d I).lower ≤ (bisectStep d I).upper ∧
      (bisectStep d I).upper ≤ I.upper := by
  cases d <;> simp only [bisectStep, RatInterval.mid] <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The bisection brackets stay ordered and inside the initial bracket. -/
lemma bisectRun_le (ds : List Bool) {I : RatInterval} (h : I.lower ≤ I.upper) :
    I.lower ≤ (bisectRun ds I).lower ∧ (bisectRun ds I).lower ≤ (bisectRun ds I).upper ∧
      (bisectRun ds I).upper ≤ I.upper := by
  induction ds generalizing I with
  | nil => exact ⟨le_rfl, h, le_rfl⟩
  | cons d ds ih =>
    obtain ⟨h₁, h₂, h₃⟩ := bisectStep_le d h
    obtain ⟨h₄, h₅, h₆⟩ := ih h₂
    rw [bisectRun]
    exact ⟨h₁.trans h₄, h₅, h₆.trans h₃⟩

/-- Certified decisions keep the sign bracket `f lower ≤ 0 ≤ f upper`. -/
lemma bisectRun_sign {f : ℝ → ℝ} (ds : List Bool) {I : RatInterval}
    (hcert : SignCertified f ds I) (hlo : f I.lower ≤ 0) (hhi : 0 ≤ f I.upper) :
    f (bisectRun ds I).lower ≤ 0 ∧ 0 ≤ f (bisectRun ds I).upper := by
  induction ds generalizing I with
  | nil => exact ⟨hlo, hhi⟩
  | cons d ds ih =>
    cases d with
    | true =>
      simp only [SignCertified] at hcert
      rw [bisectRun]
      exact ih hcert.2 hlo hcert.1
    | false =>
      simp only [SignCertified] at hcert
      rw [bisectRun]
      exact ih hcert.2 hcert.1 hhi

/-- Certified decisions exist for any number of steps, since `0 ≤ f m` or `f m ≤ 0` at every
midpoint. -/
lemma exists_signCertified (f : ℝ → ℝ) (n : ℕ) (I : RatInterval) :
    ∃ ds : List Bool, ds.length = n ∧ SignCertified f ds I := by
  induction n generalizing I with
  | zero => exact ⟨[], rfl, trivial⟩
  | succ n ih =>
    rcases le_total 0 (f I.mid) with h | h
    · obtain ⟨ds, hlen, hds⟩ := ih (bisectStep true I)
      refine ⟨true :: ds, by simp [hlen], ?_⟩
      simp only [SignCertified]
      exact ⟨h, hds⟩
    · obtain ⟨ds, hlen, hds⟩ := ih (bisectStep false I)
      refine ⟨false :: ds, by simp [hlen], ?_⟩
      simp only [SignCertified]
      exact ⟨h, hds⟩

/-- **Certified bisection bounds.** Let `f` be continuous on `[a, b]` with `a ≤ b` and
`f a ≤ 0 ≤ f b`. After `n = ds.length` certified bisection steps from `[a, b]`, the returned
rational bracket has width `(b - a) / 2 ^ n`, lies in `[a, b]`, and encloses a root of `f`. -/
lemma bisectRun_width_and_root {f : ℝ → ℝ} {a b : ℚ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc (a : ℝ) b)) (ha : f a ≤ 0) (hb : 0 ≤ f b)
    (ds : List Bool) (hcert : SignCertified f ds ⟨a, b⟩) :
    (bisectRun ds ⟨a, b⟩).width = (b - a) / 2 ^ ds.length ∧
      a ≤ (bisectRun ds ⟨a, b⟩).lower ∧ (bisectRun ds ⟨a, b⟩).upper ≤ b ∧
      ∃ c, (bisectRun ds ⟨a, b⟩).Encloses c ∧ f c = 0 := by
  obtain ⟨h₁, h₂, h₃⟩ := bisectRun_le ds (I := ⟨a, b⟩) hab
  obtain ⟨hlo, hhi⟩ := bisectRun_sign ds hcert ha hb
  have hsub : Set.Icc ((bisectRun ds ⟨a, b⟩).lower : ℝ) (bisectRun ds ⟨a, b⟩).upper ⊆
      Set.Icc (a : ℝ) b :=
    Set.Icc_subset_Icc (by exact_mod_cast h₁) (by exact_mod_cast h₃)
  obtain ⟨c, hc, hfc⟩ :=
    exists_root_of_nonpos_of_nonneg (by exact_mod_cast h₂) (hf.mono hsub) hlo hhi
  exact ⟨bisectRun_width ds ⟨a, b⟩, h₁, h₃, c, hc, hfc⟩

/-- **Certified bisection and uniqueness.** If `f` is strictly monotone on `[a, b]` with
`f a ≤ 0 ≤ f b`, then every certified bisection bracket encloses each root `c ∈ [a, b]` of `f`.
No continuity is needed for this localization. -/
lemma encloses_bisectRun_of_strictMonoOn {f : ℝ → ℝ} {a b : ℚ} (hab : a ≤ b)
    (hmono : StrictMonoOn f (Set.Icc (a : ℝ) b)) (ha : f a ≤ 0) (hb : 0 ≤ f b)
    (ds : List Bool) (hcert : SignCertified f ds ⟨a, b⟩) {c : ℝ} (hc : c ∈ Set.Icc (a : ℝ) b)
    (hfc : f c = 0) : (bisectRun ds ⟨a, b⟩).Encloses c := by
  obtain ⟨h₁, h₂, h₃⟩ := bisectRun_le ds (I := ⟨a, b⟩) hab
  obtain ⟨hlo, hhi⟩ := bisectRun_sign ds hcert ha hb
  have hlo_mem : ((bisectRun ds ⟨a, b⟩).lower : ℝ) ∈ Set.Icc (a : ℝ) b :=
    ⟨by exact_mod_cast h₁, by exact_mod_cast h₂.trans h₃⟩
  have hhi_mem : ((bisectRun ds ⟨a, b⟩).upper : ℝ) ∈ Set.Icc (a : ℝ) b :=
    ⟨by exact_mod_cast h₁.trans h₂, by exact_mod_cast h₃⟩
  refine ⟨not_lt.1 fun hlt => ?_, not_lt.1 fun hlt => ?_⟩
  · have := hmono hc hlo_mem hlt
    linarith
  · have := hmono hhi_mem hc hlt
    linarith

/-! ## D. Quadrature and Taylor truncation bounds -/

/-- **Trapezoidal rule error bound.** If `f` is `C²` on `[[a, b]]` and `|f''| ≤ ζ` on `[[a, b]]`,
then the composite trapezoidal rule with `N` subintervals has error at most
`|b - a| ^ 3 * ζ / (12 * N ^ 2)`. Mathlib's `trapezoidal_error_le_of_c2` assumes the derivative
bound at every real point; here it is needed only on the interval. -/
lemma abs_trapezoidal_error_le {f : ℝ → ℝ} {a b ζ : ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ 2 f (Set.uIcc a b))
    (hζ : ∀ x ∈ Set.uIcc a b, |iteratedDerivWithin 2 f (Set.uIcc a b) x| ≤ ζ) (hN : 0 < N) :
    |trapezoidal_error f N a b| ≤ |b - a| ^ 3 * ζ / (12 * N ^ 2) := by
  refine trapezoidal_error_le_of_c2 hf (fun x => ?_) hN
  by_cases hx : x ∈ Set.uIcc a b
  · exact hζ x hx
  · have hcl : x ∉ closure (Set.uIcc a b) := by
      rwa [show closure (Set.uIcc a b) = Set.uIcc a b from isClosed_Icc.closure_eq]
    rw [iteratedDerivWithin_succ, derivWithin_zero_of_notMem_closure hcl, abs_zero]
    exact (abs_nonneg _).trans (hζ a Set.left_mem_uIcc)

/-- **Taylor truncation bound** (Lagrange form). If `f` is `C^(n+1)` on `[[x₀, x]]` and
`|f^(n+1)| ≤ C` strictly between `x₀` and `x`, then the degree-`n` Taylor polynomial of `f` at `x₀`
approximates `f x` to within `C * |x - x₀| ^ (n + 1) / (n + 1)!`. -/
lemma abs_sub_taylorWithinEval_le {f : ℝ → ℝ} {x₀ x C : ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 1) f (Set.uIcc x₀ x))
    (hC : ∀ y ∈ Set.uIoo x₀ x, |iteratedDeriv (n + 1) f y| ≤ C) :
    |f x - taylorWithinEval f n (Set.uIcc x₀ x) x₀ x| ≤
      C * |x - x₀| ^ (n + 1) / (n + 1).factorial := by
  rcases eq_or_ne x₀ x with rfl | hne
  · simp [taylorWithinEval_self]
  · obtain ⟨y, hy, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne hf
    rw [hrem, abs_div, abs_mul, abs_pow, Nat.abs_cast]
    gcongr
    exact hC y hy

/-- **Taylor truncation bound** with the explicit polynomial
`∑ k ≤ n, f^(k) x₀ / k! * (x - x₀) ^ k`: if `f` is of class `C^(n+1)` on `ℝ` and
`|f^(n+1)| ≤ C` strictly between `x₀` and `x`, the error is at most
`C * |x - x₀| ^ (n + 1) / (n + 1)!`. -/
lemma abs_sub_taylor_sum_le {f : ℝ → ℝ} {x₀ x C : ℝ} {n : ℕ} (hf : ContDiff ℝ (n + 1) f)
    (hC : ∀ y ∈ Set.uIoo x₀ x, |iteratedDeriv (n + 1) f y| ≤ C) :
    |f x - ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f x₀ / k.factorial * (x - x₀) ^ k| ≤
      C * |x - x₀| ^ (n + 1) / (n + 1).factorial := by
  rcases eq_or_ne x₀ x with rfl | hne
  · rw [Finset.sum_range_succ']
    simp
  · have htaylor : taylorWithinEval f n (Set.uIcc x₀ x) x₀ x =
        ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f x₀ / k.factorial * (x - x₀) ^ k := by
      rw [taylor_within_apply]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : (k : WithTop ℕ∞) ≤ n + 1 := by
        exact_mod_cast (Finset.mem_range.1 hk).le
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
        (hf.contDiffAt.of_le hk') Set.left_mem_uIcc, smul_eq_mul]
      ring
    rw [← htaylor]
    exact abs_sub_taylorWithinEval_le hf.contDiffOn hC

/-! ## E. Error budgets -/

/-- **Error budget.** Let `approx` be a computed value, and `exactMeas`, `exactTrue` the exact
outputs at the measured data `dMeas` and the true data `dTrue`. Assume the numerical error bound
`|approx - exactMeas| ≤ εnum`, the conditioning hypothesis
`|exactMeas - exactTrue| ≤ K * |dMeas - dTrue|`, and the data-uncertainty bound
`|dMeas - dTrue| ≤ εdata`. Then the total error is at most `εnum + K * εdata`. -/
lemma abs_sub_le_numerical_add_data {approx exactMeas exactTrue dMeas dTrue εnum εdata : ℝ}
    {K : NNReal} (hnum : |approx - exactMeas| ≤ εnum)
    (hcond : |exactMeas - exactTrue| ≤ K * |dMeas - dTrue|) (hdata : |dMeas - dTrue| ≤ εdata) :
    |approx - exactTrue| ≤ εnum + K * εdata := by
  have hprop : |exactMeas - exactTrue| ≤ K * εdata :=
    hcond.trans (mul_le_mul_of_nonneg_left hdata K.coe_nonneg)
  calc |approx - exactTrue| ≤ |approx - exactMeas| + |exactMeas - exactTrue| :=
        abs_sub_le _ _ _
    _ ≤ εnum + K * εdata := add_le_add hnum hprop

/-- **Error budget for a Lipschitz model.** If the model `F` is `K`-Lipschitz on a set containing
the measured and true data, `|approx - F dMeas| ≤ εnum` and `|dMeas - dTrue| ≤ εdata`, then
`|approx - F dTrue| ≤ εnum + K * εdata`. -/
lemma abs_sub_le_numerical_add_data_of_lipschitzOnWith {F : ℝ → ℝ} {s : Set ℝ} {K : NNReal}
    (hF : LipschitzOnWith K F s) {approx dMeas dTrue εnum εdata : ℝ} (hmeas : dMeas ∈ s)
    (htrue : dTrue ∈ s) (hnum : |approx - F dMeas| ≤ εnum) (hdata : |dMeas - dTrue| ≤ εdata) :
    |approx - F dTrue| ≤ εnum + K * εdata := by
  refine abs_sub_le_numerical_add_data hnum ?_ hdata
  simpa [Real.dist_eq] using hF.dist_le_mul dMeas hmeas dTrue htrue

/-- **Residual bounds need conditioning.** If `g` satisfies the conditioning hypothesis
`m * |y - z| ≤ |g y - g z|` on `s` with `0 < m`, `xs ∈ s` is a root of `g`, and `x ∈ s` has
residual `|g x| ≤ τ`, then `|x - xs| ≤ τ / m`. -/
lemma abs_sub_root_le_of_residual {g : ℝ → ℝ} {s : Set ℝ} {m τ x xs : ℝ} (hm : 0 < m)
    (hcond : ∀ y ∈ s, ∀ z ∈ s, m * |y - z| ≤ |g y - g z|) (hx : x ∈ s) (hxs : xs ∈ s)
    (hroot : g xs = 0) (hres : |g x| ≤ τ) : |x - xs| ≤ τ / m := by
  rw [le_div_iff₀ hm, mul_comm]
  calc m * |x - xs| ≤ |g x - g xs| := hcond x hx xs hxs
    _ = |g x| := by rw [hroot, sub_zero]
    _ ≤ τ := hres

/-- Conditioning of `x ↦ x + h x` for monotone `h`: it does not contract distances, so solutions of
`x + h x = c` depend `1`-Lipschitz on `c`. -/
lemma abs_sub_le_abs_add_sub_add {h : ℝ → ℝ} (hh : Monotone h) (x y : ℝ) :
    |x - y| ≤ |(x + h x) - (y + h y)| := by
  rcases le_total x y with hxy | hxy
  · have := hh hxy
    rw [abs_of_nonpos (sub_nonpos.2 hxy), abs_of_nonpos (by linarith)]
    linarith
  · have := hh hxy
    rw [abs_of_nonneg (sub_nonneg.2 hxy), abs_of_nonneg (by linarith)]
    linarith

/-! ## F. Provenance records -/

/-- Provenance of a numerical capstone. Units and data version are plain strings naming the unit
system, the unit of the reported quantity and the source data; no dimensional analysis is
performed. -/
structure Provenance where
  /-- The unit system and the unit of the reported quantity, e.g. `"SI; dimensionless"`. -/
  units : String
  /-- The version identifier of the source data. -/
  dataVersion : String
  /-- The tolerance: a bound on the width of the certified bracket, so that every point of the
  bracket is within this distance of the true value. -/
  tolerance : ℚ
  /-- The Mathlib lemmas cited by the certificate. Name literals such as `` ``Real.exp_bound ``
  are checked to exist when the record is elaborated; that the proof uses them is not checked. -/
  lemmas : List Lean.Name

/-- A certified root of `f`, recorded with the exact rational computation that encloses it: an
initial bracket and the decisions of a bisection run (with no decisions, the initial bracket
itself is the enclosure), the unique root of `f` in the initial bracket, and a provenance record
whose tolerance bounds the width of the final bracket. -/
structure CertifiedRoot (f : ℝ → ℝ) where
  /-- The initial rational bracket. -/
  bracket : RatInterval
  /-- The recorded bisection decisions. -/
  decisions : List Bool
  /-- The root. -/
  root : ℝ
  /-- The root solves the equation. -/
  apply_root_eq_zero : f root = 0
  /-- The equation has at most one solution in the initial bracket. -/
  zeros_subsingleton : {x ∈ Set.Icc (bracket.lower : ℝ) bracket.upper | f x = 0}.Subsingleton
  /-- The final bracket of the recorded run encloses the root. -/
  encloses_root : (bisectRun decisions bracket).Encloses root
  /-- Units, data version, tolerance and the cited lemmas. -/
  provenance : Provenance
  /-- The width of the final bracket is within the recorded tolerance. -/
  width_le_tolerance : (bisectRun decisions bracket).width ≤ provenance.tolerance

namespace CertifiedRoot

/-- The certified enclosure of the root: the final bracket of the recorded run. -/
def enclosure {f : ℝ → ℝ} (r : CertifiedRoot f) : RatInterval :=
  bisectRun r.decisions r.bracket

/-- The root lies in the initial bracket. -/
lemma root_mem {f : ℝ → ℝ} (r : CertifiedRoot f) :
    r.root ∈ Set.Icc (r.bracket.lower : ℝ) r.bracket.upper := by
  have h := r.encloses_root
  have hw : 0 ≤ r.bracket.width / 2 ^ r.decisions.length :=
    bisectRun_width r.decisions r.bracket ▸ h.width_nonneg
  have hle : r.bracket.lower ≤ r.bracket.upper := by
    have : 0 ≤ r.bracket.width := by
      simpa using mul_nonneg hw (pow_nonneg (by norm_num : (0 : ℚ) ≤ 2) r.decisions.length)
    exact sub_nonneg.1 this
  obtain ⟨h₁, -, h₃⟩ := bisectRun_le r.decisions hle
  exact ⟨(Rat.cast_le.2 h₁).trans h.1, h.2.trans (Rat.cast_le.2 h₃)⟩

/-- Every solution of the equation in the initial bracket is the certified root. -/
lemma eq_root {f : ℝ → ℝ} (r : CertifiedRoot f) {x : ℝ}
    (hx : x ∈ Set.Icc (r.bracket.lower : ℝ) r.bracket.upper) (hfx : f x = 0) : x = r.root :=
  r.zeros_subsingleton ⟨hx, hfx⟩ ⟨r.root_mem, r.apply_root_eq_zero⟩

/-- The midpoint of the certified enclosure is within half of the recorded tolerance of the
root. -/
lemma abs_sub_mid_le {f : ℝ → ℝ} (r : CertifiedRoot f) :
    |r.root - r.enclosure.mid| ≤ (r.provenance.tolerance : ℝ) / 2 := by
  have h := r.encloses_root.abs_sub_mid_le
  have ht : ((bisectRun r.decisions r.bracket).width : ℝ) ≤ r.provenance.tolerance := by
    exact_mod_cast r.width_le_tolerance
  rw [enclosure]
  linarith

/-- The certified root obtained from a certified bisection run on `[a, b]` for a function that is
continuous and strictly monotone on `[a, b]` with `f a ≤ 0 ≤ f b`, provided the final width
`(b - a) / 2 ^ n` meets the recorded tolerance. -/
noncomputable def ofBisection {f : ℝ → ℝ} {a b : ℚ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc (a : ℝ) b)) (hmono : StrictMonoOn f (Set.Icc (a : ℝ) b))
    (ha : f a ≤ 0) (hb : 0 ≤ f b) (ds : List Bool) (hcert : SignCertified f ds ⟨a, b⟩)
    (p : Provenance) (htol : (b - a) / 2 ^ ds.length ≤ p.tolerance) : CertifiedRoot f :=
  have h := bisectRun_width_and_root hab hf ha hb ds hcert
  { bracket := ⟨a, b⟩
    decisions := ds
    root := h.2.2.2.choose
    apply_root_eq_zero := h.2.2.2.choose_spec.2
    zeros_subsingleton := fun _ hx _ hy => hmono.injOn hx.1 hy.1 (hx.2.trans hy.2.symm)
    encloses_root := h.2.2.2.choose_spec.1
    provenance := p
    width_le_tolerance := h.1.trans_le htol }

end CertifiedRoot

/-! ## G. Capstone: `x + exp x = 2` -/

/-- The recorded decisions of ten bisection steps for `x + exp x - 2` on `[0, 1]`. -/
def equilibriumDecisions : List Bool :=
  [true, false, false, false, true, true, true, false, true, false]

private lemma equilibrium_nonneg {q : ℚ} (hq : |q| ≤ 1) (h : 2 ≤ q + (expInterval q 6).lower) :
    0 ≤ (q : ℝ) + Real.exp q - 2 := by
  have he := (encloses_expInterval hq (by norm_num : 0 < 6)).1
  have h' : ((2 : ℚ) : ℝ) ≤ ((q + (expInterval q 6).lower : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

private lemma equilibrium_nonpos {q : ℚ} (hq : |q| ≤ 1) (h : q + (expInterval q 6).upper ≤ 2) :
    (q : ℝ) + Real.exp q - 2 ≤ 0 := by
  have he := (encloses_expInterval hq (by norm_num : 0 < 6)).2
  have h' : ((q + (expInterval q 6).upper : ℚ) : ℝ) ≤ ((2 : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

private lemma equilibrium_one : 0 ≤ (1 : ℝ) + Real.exp 1 - 2 := by
  linarith [Real.add_one_le_exp 1]

/-- The equilibrium equation is monotone: `x ↦ x + exp x - 2` is strictly increasing on `ℝ`. -/
lemma equilibrium_strictMono : StrictMono fun x : ℝ => x + Real.exp x - 2 :=
  fun _ _ hxy => by linarith [Real.exp_lt_exp.2 hxy]

/-- The recorded decisions are certified: the sign of `x + exp x - 2` at each of the ten midpoints
is checked by exact rational arithmetic on the six-term enclosure `expInterval q 6`. -/
lemma signCertified_equilibrium :
    SignCertified (fun x : ℝ => x + Real.exp x - 2) equilibriumDecisions ⟨0, 1⟩ := by
  simp only [equilibriumDecisions, SignCertified, bisectStep]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals first
    | exact equilibrium_nonneg (by norm_num [RatInterval.mid, abs_le])
        (by norm_num [RatInterval.mid, expInterval, expPartialSum, expRemainderBound,
          Finset.sum_range_succ, Nat.factorial, abs_of_nonneg])
    | exact equilibrium_nonpos (by norm_num [RatInterval.mid, abs_le])
        (by norm_num [RatInterval.mid, expInterval, expPartialSum, expRemainderBound,
          Finset.sum_range_succ, Nat.factorial, abs_of_nonneg])

/-- **Capstone.** The unique root of the equilibrium equation `x + exp x = 2` in `[0, 1]`,
certified by ten bisection steps in the bracket `[453/1024, 227/512]` of width `1/1024`, within the
recorded tolerance `1/1000`. The constant `2` is exact rational data, and `x` is dimensionless, as
the argument of `exp` must be. -/
noncomputable def equilibriumCapstone : CertifiedRoot (fun x : ℝ => x + Real.exp x - 2) :=
  CertifiedRoot.ofBisection (a := 0) (b := 1) (by norm_num) (by fun_prop)
    (equilibrium_strictMono.strictMonoOn _) (by norm_num) (by simpa using equilibrium_one)
    equilibriumDecisions signCertified_equilibrium
    { units := "SI; dimensionless"
      dataVersion := "exact rational constant c = 2, no measured data"
      tolerance := 1 / 1000
      lemmas := [``Real.exp_bound, ``intermediate_value_Icc, ``StrictMonoOn.injOn] }
    (by norm_num [equilibriumDecisions])

/-- The recorded run is exact rational arithmetic: the ten steps from `[0, 1]` end in
`[453/1024, 227/512]`. -/
lemma bisectRun_equilibriumDecisions :
    bisectRun equilibriumDecisions ⟨0, 1⟩ = ⟨453 / 1024, 227 / 512⟩ := by
  norm_num [equilibriumDecisions, bisectRun, bisectStep, RatInterval.mid]

/-- The certified enclosure of the capstone root is `[453/1024, 227/512]`. -/
lemma equilibriumCapstone_enclosure :
    equilibriumCapstone.enclosure = ⟨453 / 1024, 227 / 512⟩ :=
  bisectRun_equilibriumDecisions

end MathlibExt.Analysis.Numerical.Certified
