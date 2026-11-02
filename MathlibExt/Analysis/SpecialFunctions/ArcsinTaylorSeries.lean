/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

import Mathlib.Algebra.Polynomial.Smeval
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Data.Nat.Choose.Central
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace MathlibExt.Analysis.SpecialFunctions.ArcsinTaylorSeries

noncomputable section

private lemma centralBinomial_div_pow_le_one (n : ℕ) :
    (Nat.choose (2 * n) n : ℝ) / (2 : ℝ) ^ (2 * n) ≤ 1 := by
  have hpos : (0 : ℝ) < 2 ^ (2 * n) := by positivity
  rw [div_le_one hpos]
  have h := Nat.choose_le_two_pow (2 * n) n
  have hcast : (Nat.choose (2 * n) n : ℝ) ≤ ((2 ^ (2 * n) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hcast
  linarith

private lemma summable_one_div_nat_add_one_sq :
    Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) ^ 2)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).mpr h
  have hcongr : (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) ^ 2)) =
      (fun n : ℕ => (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) ^ 2)) := by
    funext k
    rw [Nat.cast_add, Nat.cast_one]
  rwa [hcongr]

private lemma cast_two_mul_add_one (k : ℕ) :
    (((2 * k + 1 : ℕ)) : ℝ) = 2 * (k : ℝ) + 1 := by
  push_cast
  ring

private lemma rawTerm_norm_le (t : ℝ) (ht : ‖t‖ ≤ 1) (k : ℕ) :
    ‖(Nat.choose (2 * k) k : ℝ) * t ^ (2 * k + 1) /
        ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))‖ ≤
      (1 : ℝ) / (((k : ℝ) + 1) ^ 2) := by
  have hMpos : (0 : ℝ) < ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
    positivity
  have hDpos : (0 : ℝ) < (2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
    positivity
  rw [norm_div, norm_mul, norm_mul]
  have hchoose : ‖(Nat.choose (2 * k) k : ℝ)‖ = (Nat.choose (2 * k) k : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  have hpow2 : ‖((2 : ℝ) ^ (2 * k))‖ = (2 : ℝ) ^ (2 * k) :=
    abs_of_nonneg (by positivity)
  have hsq : ‖(((((2 * k + 1 : ℕ)) : ℝ) ^ 2))‖ = ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
    abs_of_nonneg (by positivity)
  rw [hchoose, norm_pow, hpow2, hsq]
  have hc : (Nat.choose (2 * k) k : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by
    have h2pos : (0 : ℝ) < 2 ^ (2 * k) := by positivity
    have h := centralBinomial_div_pow_le_one k
    rwa [div_le_one h2pos] at h
  have ht2 : ‖t‖ ^ (2 * k + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) ht
  have hnum : (Nat.choose (2 * k) k : ℝ) * ‖t‖ ^ (2 * k + 1) ≤
      (2 : ℝ) ^ (2 * k) * 1 :=
    mul_le_mul hc ht2 (by positivity) (by positivity)
  have hbase : (((k : ℝ) + 1) ^ 2) ≤ ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
    rw [cast_two_mul_add_one]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hqpos : (0 : ℝ) < (((k : ℝ) + 1) ^ 2) := by positivity
  calc (Nat.choose (2 * k) k : ℝ) * ‖t‖ ^ (2 * k + 1) /
          ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))
        ≤ ((2 : ℝ) ^ (2 * k) * 1) / ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) :=
          (div_le_div_iff_of_pos_right hDpos).mpr hnum
      _ = 1 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
          field_simp
      _ ≤ 1 / (((k : ℝ) + 1) ^ 2) :=
          one_div_le_one_div_of_le hqpos hbase

/-- **Normalized central binomial coefficient.** For a natural number $n$, the normalized central
binomial coefficient is the real number $c_n = \binom{2n}{n}/2^{2n} = \binom{2n}{n}/4^n$. -/
def centralBinomialCoeff (n : ℕ) : ℝ :=
  (Nat.choose (2 * n) n : ℝ) / (2 : ℝ) ^ (2 * n)

/-- **Normalized central binomial coefficients are nonnegative.** For every natural number $n$,
$0 \le \binom{2n}{n}/4^n$. -/
lemma centralBinomialCoeff_nonneg (n : ℕ) : 0 ≤ centralBinomialCoeff n := by
  unfold centralBinomialCoeff
  positivity

/-- **Normalized central binomial coefficients are at most one.** For every natural number $n$,
$\binom{2n}{n}/4^n \le 1$. -/
lemma centralBinomialCoeff_le_one (n : ℕ) : centralBinomialCoeff n ≤ 1 :=
  centralBinomial_div_pow_le_one n

/-- **Arcsine Taylor series.** Let $c_n = \binom{2n}{n}/4^n$. For real $t$, the arcsine Taylor
series is

$$S(t) = \sum_{n=0}^{\infty} \frac{c_n\, t^{2n+1}}{2n+1},$$

with the convention that the sum is $0$ when the series is not summable.
-/
def arcsinSeries (t : ℝ) : ℝ :=
  ∑' n : ℕ, centralBinomialCoeff n * t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)

/-- **Integrated arcsine series.** Let $c_n = \binom{2n}{n}/4^n$. For real $t$, the integrated
arcsine series is

$$F(t) = \sum_{n=0}^{\infty} \frac{c_n\, t^{2n+1}}{(2n+1)^2},$$

with the convention that the sum is $0$ when the series is not summable.

Each term is the antiderivative vanishing at $0$ of the corresponding term $c_n t^{2n}/(2n+1)$
of $S(t)/t$, where $S(t) = \sum_{n \ge 0} c_n t^{2n+1}/(2n+1)$ is the arcsine Taylor series.
-/
def arcsinIntegralSeries (t : ℝ) : ℝ :=
  ∑' n : ℕ, centralBinomialCoeff n * t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ^ 2

private lemma cast_centralBinom_succ (n : ℕ) :
    ((n : ℝ) + 1) * ((Nat.choose (2 * (n + 1)) (n + 1) : ℕ) : ℝ)
      = 2 * (2 * (n : ℝ) + 1) * ((Nat.choose (2 * n) n : ℕ) : ℝ) := by
  have h := Nat.succ_mul_centralBinom_succ n
  have hcast : ((n + 1 : ℕ) : ℝ) * ((Nat.centralBinom (n + 1) : ℕ) : ℝ)
      = 2 * ((2 * n + 1 : ℕ) : ℝ) * ((Nat.centralBinom n : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [show Nat.centralBinom (n + 1) = Nat.choose (2 * (n + 1)) (n + 1) from rfl,
    show Nat.centralBinom n = Nat.choose (2 * n) n from rfl] at hcast
  push_cast at hcast
  linear_combination hcast

private lemma centralBinomialCoeff_succ (n : ℕ) :
    centralBinomialCoeff (n + 1)
      = centralBinomialCoeff n * ((2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))) := by
  have h2 := cast_centralBinom_succ n
  have hne1 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
  have hPne : (2 : ℝ) ^ (2 * n) ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ (2 * (n + 1)) = 4 * (2 : ℝ) ^ (2 * n) := by
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]
    ring
  unfold centralBinomialCoeff
  rw [hpow]
  field_simp
  linarith [h2]

private lemma smeval_ascPochhammer_succ (n : ℕ) :
    (ascPochhammer ℕ (n + 1)).smeval (1 / 2 : ℝ)
      = (ascPochhammer ℕ n).smeval (1 / 2 : ℝ) * ((1 / 2 : ℝ) + (n : ℝ)) := by
  rw [ascPochhammer_succ_right, Polynomial.smeval_mul]
  congr 1
  rw [Polynomial.smeval_add, Polynomial.smeval_X, Polynomial.smeval_natCast]
  simp only [pow_one, pow_zero, nsmul_eq_mul, mul_one]

private lemma multichoose_half_succ (n : ℕ) :
    Ring.multichoose (1 / 2 : ℝ) (n + 1)
      = Ring.multichoose (1 / 2 : ℝ) n * (((n : ℝ) + 1 / 2) / ((n : ℝ) + 1)) := by
  have hP := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1 / 2 : ℝ) n
  have hP1 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1 / 2 : ℝ) (n + 1)
  rw [nsmul_eq_mul] at hP hP1
  have hfact : ((n + 1).factorial : ℝ)
      = ((n : ℝ) + 1) * ((n.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hrec := smeval_ascPochhammer_succ n
  have hne1 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
  have hPne : ((n.factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [hfact, hrec, ← hP] at hP1
  have key : ((n : ℝ) + 1) * Ring.multichoose (1 / 2 : ℝ) (n + 1)
      = ((n : ℝ) + 1 / 2) * Ring.multichoose (1 / 2 : ℝ) n := by
    apply mul_left_cancel₀ hPne
    linear_combination hP1
  rw [← mul_div_assoc, eq_div_iff hne1]
  linear_combination key

private lemma multichoose_half_eq_centralBinomialCoeff (n : ℕ) :
    Ring.multichoose (1 / 2 : ℝ) n = centralBinomialCoeff n := by
  induction n with
  | zero =>
    simp [centralBinomialCoeff]
  | succ n ih =>
    have hne1 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
    have hne2 : 2 * ((n : ℝ) + 1) ≠ 0 := mul_ne_zero (by norm_num) hne1
    rw [multichoose_half_succ, centralBinomialCoeff_succ, ih]
    congr 1
    field_simp

private lemma centralBinomial_hasSum {s : ℝ} (hs : ‖s‖ < 1) :
    HasSum (fun n : ℕ => centralBinomialCoeff n * s ^ n) (1 / (1 - s) ^ (1 / 2 : ℝ)) := by
  have h0 := Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2 : ℝ)
  have hmem : s ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right]
    exact ENNReal.ofReal_lt_one.mpr hs
  have hsum := h0.hasSum hmem
  rw [zero_add] at hsum
  refine hsum.congr_fun (fun n => ?_)
  rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    ← Ring.multichoose_eq, multichoose_half_eq_centralBinomialCoeff]

private lemma centralBinomial_even_hasSum {y : ℝ} (hy : ‖y‖ < 1) :
    HasSum (fun n : ℕ => centralBinomialCoeff n * y ^ (2 * n)) (1 / √(1 - y ^ 2)) := by
  have hs : ‖y ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hy (by norm_num)
  have h := centralBinomial_hasSum hs
  have hfun : (fun n : ℕ => centralBinomialCoeff n * y ^ (2 * n)) =
      (fun n : ℕ => centralBinomialCoeff n * (y ^ 2) ^ n) := by
    funext n
    rw [← pow_mul]
  rw [hfun]
  have hval : (1 : ℝ) / (1 - y ^ 2) ^ (1 / 2 : ℝ) = 1 / √(1 - y ^ 2) := by
    rw [Real.sqrt_eq_rpow]
  rwa [hval] at h

private lemma arcsinSeries_term_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => centralBinomialCoeff n * s ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ))
      (centralBinomialCoeff n * t ^ (2 * n)) t := by
  have hpow : HasDerivAt (fun s : ℝ => s ^ (2 * n + 1))
      (((2 * n + 1 : ℕ) : ℝ) * t ^ (2 * n)) t := by
    have h := hasDerivAt_pow (2 * n + 1) t
    have heq : (2 * n + 1) - 1 = 2 * n := by omega
    rwa [heq] at h
  have hmul := hpow.const_mul (centralBinomialCoeff n)
  have hdiv := hmul.div_const ((2 * n + 1 : ℕ) : ℝ)
  have hsimp : centralBinomialCoeff n * (((2 * n + 1 : ℕ) : ℝ) * t ^ (2 * n)) /
        ((2 * n + 1 : ℕ) : ℝ) = centralBinomialCoeff n * t ^ (2 * n) := by
    field_simp
  rwa [hsimp] at hdiv

private lemma arcsinSeries_deriv_majorant (r : ℝ) (_hr0 : 0 < r) (_hr1 : r < 1) (n : ℕ) (y : ℝ)
    (hy : y ∈ Set.Ioo (-r) r) :
    ‖centralBinomialCoeff n * y ^ (2 * n)‖ ≤ (r ^ 2) ^ n := by
  have hyr : ‖y‖ < r := by
    rw [Real.norm_eq_abs]
    rw [Set.mem_Ioo] at hy
    rw [abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hc : ‖centralBinomialCoeff n‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (centralBinomialCoeff_nonneg n)]
    exact centralBinomialCoeff_le_one n
  calc ‖centralBinomialCoeff n * y ^ (2 * n)‖
        = ‖centralBinomialCoeff n‖ * ‖y‖ ^ (2 * n) := by rw [norm_mul, norm_pow]
      _ ≤ 1 * r ^ (2 * n) := by
          apply mul_le_mul hc _ (by positivity) (by norm_num)
          exact pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hyr) _
      _ = (r ^ 2) ^ n := by ring

private lemma arcsinSeries_hasDerivAt_of_mem {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hy : y ∈ Set.Ioo (-r) r) :
    HasDerivAt arcsinSeries (∑' n : ℕ, centralBinomialCoeff n * y ^ (2 * n)) y := by
  have hu : Summable (fun n : ℕ => (r ^ 2) ^ n) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hr0, hr1]
  have hopen : IsOpen (Set.Ioo (-r : ℝ) r) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (-r : ℝ) r) := isPreconnected_Ioo
  have hderiv : ∀ n : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      HasDerivAt (fun s : ℝ => centralBinomialCoeff n * s ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ))
        (centralBinomialCoeff n * z ^ (2 * n)) z :=
    fun n z _ => arcsinSeries_term_hasDerivAt n z
  have hbound : ∀ n : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      ‖centralBinomialCoeff n * z ^ (2 * n)‖ ≤ (r ^ 2) ^ n :=
    fun n z hz => arcsinSeries_deriv_majorant r hr0 hr1 n z hz
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-r : ℝ) r := by simp [Set.mem_Ioo, hr0]
  have hsum0 : Summable (fun n : ℕ =>
      centralBinomialCoeff n * (0 : ℝ) ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) := by
    apply Summable.of_norm
    have hle : ∀ n : ℕ,
        ‖centralBinomialCoeff n * (0 : ℝ) ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)‖ ≤
          (1 : ℝ) / (((n : ℝ) + 1) ^ 2) := by
      intro n
      by_cases hn : n = 0
      · subst hn
        simp [centralBinomialCoeff]
      · have hz : (0 : ℝ) ^ (2 * n + 1) = 0 := zero_pow (by omega)
        rw [hz]
        simp only [mul_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
          zero_div, norm_zero, one_div, inv_nonneg, ge_iff_le]
        positivity
    have haux : Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) ^ 2)) := by
      have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
        (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      have hshift : Summable (fun n : ℕ => (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) ^ 2)) :=
        (summable_nat_add_iff 1).mpr h
      have hcongr : (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) ^ 2)) =
          (fun n : ℕ => (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) ^ 2)) := by
        funext k
        rw [Nat.cast_add, Nat.cast_one]
      rwa [hcongr]
    exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle haux
  exact hasDerivAt_tsum_of_isPreconnected hu hopen hpre hderiv hbound hy0 hsum0 hy

private lemma mem_Ioo_norm_lt_one (y : ℝ) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖y‖ < 1 := by
  rw [Set.mem_Ioo] at hy
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> linarith [hy.1, hy.2]

private lemma arcsinSeries_zero : arcsinSeries 0 = 0 := by
  unfold arcsinSeries
  have hzero : (fun n : ℕ => centralBinomialCoeff n * (0 : ℝ) ^ (2 * n + 1) /
      ((2 * n + 1 : ℕ) : ℝ)) = fun _ => 0 := by
    funext n
    have hz : (0 : ℝ) ^ (2 * n + 1) = 0 := zero_pow (by omega)
    rw [hz]
    simp
  rw [hzero, tsum_zero]

private lemma arcsinSeries_hasDerivAt_sqrt {y : ℝ} (hy : ‖y‖ < 1) :
    HasDerivAt arcsinSeries (1 / √(1 - y ^ 2)) y := by
  have hr1 : (‖y‖ + 1) / 2 < 1 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith [hy]
  have hr0 : (0 : ℝ) < (‖y‖ + 1) / 2 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith
  have habs : |y| < (‖y‖ + 1) / 2 := by
    rw [← Real.norm_eq_abs]
    linarith [hy]
  rw [abs_lt] at habs
  have hymem : y ∈ Set.Ioo (-((‖y‖ + 1) / 2)) ((‖y‖ + 1) / 2) := by
    rw [Set.mem_Ioo]
    constructor <;> linarith [habs.1, habs.2]
  have hder := arcsinSeries_hasDerivAt_of_mem hr0 hr1 hymem
  have hsum := centralBinomial_even_hasSum hy
  rw [hsum.tsum_eq] at hder
  exact hder

/-- **Taylor series of the arcsine.** For every real $t$ with $|t| < 1$,

$$\arcsin t = \sum_{n=0}^{\infty} \frac{\binom{2n}{n}}{4^n} \cdot \frac{t^{2n+1}}{2n+1}.$$
-/
theorem arcsinSeries_eq_arcsin :
    Set.EqOn arcsinSeries Real.arcsin (Set.Ioo (-1 : ℝ) 1) := by
  have hopen : IsOpen (Set.Ioo (-1 : ℝ) 1) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (-1 : ℝ) 1) := isPreconnected_Ioo
  have hGdiff : DifferentiableOn ℝ arcsinSeries (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    have hnorm := mem_Ioo_norm_lt_one x hx
    have h := arcsinSeries_hasDerivAt_sqrt hnorm
    exact (h.differentiableAt).differentiableWithinAt
  have harcsin_diff : DifferentiableOn ℝ Real.arcsin (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    rw [Set.mem_Ioo] at hx
    have h1 : x ≠ -1 := by linarith [hx.1]
    have h2 : x ≠ 1 := by linarith [hx.2]
    exact ((Real.hasDerivAt_arcsin h1 h2).differentiableAt).differentiableWithinAt
  have hderiv_eq : Set.EqOn (deriv arcsinSeries) (deriv Real.arcsin) (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    have hnorm := mem_Ioo_norm_lt_one x hx
    have hG := arcsinSeries_hasDerivAt_sqrt hnorm
    rw [Set.mem_Ioo] at hx
    have h1 : x ≠ -1 := by linarith [hx.1]
    have h2 : x ≠ 1 := by linarith [hx.2]
    have hA := Real.hasDerivAt_arcsin h1 h2
    rw [hG.deriv, hA.deriv]
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have h0eq : arcsinSeries 0 = Real.arcsin 0 := by rw [arcsinSeries_zero, Real.arcsin_zero]
  exact IsOpen.eqOn_of_deriv_eq hopen hpre hGdiff harcsin_diff hderiv_eq h0mem h0eq

private lemma arcsinIntegralSeries_term_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => centralBinomialCoeff n * s ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ^ 2)
      (centralBinomialCoeff n * t ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ)) t := by
  have hpow : HasDerivAt (fun s : ℝ => s ^ (2 * n + 1))
      (((2 * n + 1 : ℕ) : ℝ) * t ^ (2 * n)) t := by
    have h := hasDerivAt_pow (2 * n + 1) t
    have heq : (2 * n + 1) - 1 = 2 * n := by omega
    rwa [heq] at h
  have hmul := hpow.const_mul (centralBinomialCoeff n)
  have hdiv := hmul.div_const (((2 * n + 1 : ℕ) : ℝ) ^ 2)
  have hsimp : centralBinomialCoeff n * (((2 * n + 1 : ℕ) : ℝ) * t ^ (2 * n)) /
        ((2 * n + 1 : ℕ) : ℝ) ^ 2
      = centralBinomialCoeff n * t ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ) := by
    field_simp
  rwa [hsimp] at hdiv

/-- **Terms of the integrated arcsine series.** Let $c_n = \binom{2n}{n}/4^n$ be the normalized
central binomial coefficient. For every natural number $n$ and every real $t$,

$$\frac{c_n\, t^{2n+1}}{(2n+1)^2} = \frac{\binom{2n}{n}\, t^{2n+1}}{2^{2n}\,(2n+1)^2}.$$
-/
lemma arcsinIntegralSeries_term_eq (n : ℕ) (t : ℝ) :
    centralBinomialCoeff n * t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ^ 2
      = (Nat.choose (2 * n) n : ℝ) * t ^ (2 * n + 1) /
        ((2 : ℝ) ^ (2 * n) * ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)) := by
  unfold centralBinomialCoeff
  field_simp

/-- **Bound on the terms of the integrated arcsine series.** Write $c_k = \binom{2k}{k}/4^k$ for
the normalized central binomial coefficient. For every real number $t$ with $|t| \le 1$ and every
natural number $k$, $\left|\frac{c_k\, t^{2k+1}}{(2k+1)^2}\right| \le \frac{1}{(k+1)^2}$. -/
lemma norm_arcsinIntegralSeries_term_le (t : ℝ) (ht : ‖t‖ ≤ 1) (k : ℕ) :
    ‖centralBinomialCoeff k * t ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) ^ 2‖ ≤
      (1 : ℝ) / (((k : ℝ) + 1) ^ 2) := by
  rw [arcsinIntegralSeries_term_eq]
  exact rawTerm_norm_le t ht k

/-- **Summability of the integrated arcsine series.** Write $c_n = \binom{2n}{n}/4^n$ for the
normalized central binomial coefficient. For every real number $t$ with $|t| \le 1$, the series
$\sum_{n=0}^{\infty} \frac{c_n\, t^{2n+1}}{(2n+1)^2}$ converges absolutely. -/
theorem summable_arcsinIntegralSeries_term (t : ℝ) (ht : ‖t‖ ≤ 1) :
    Summable (fun n : ℕ =>
      centralBinomialCoeff n * t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => norm_arcsinIntegralSeries_term_le t ht n) summable_one_div_nat_add_one_sq

/-- **The integrated arcsine series vanishes at the origin.** The integrated arcsine series
$F(t) = \sum_{n \ge 0} \binom{2n}{n} 4^{-n}\, t^{2n+1}/(2n+1)^2$ satisfies $F(0) = 0$. -/
@[simp] theorem arcsinIntegralSeries_zero : arcsinIntegralSeries 0 = 0 := by
  unfold arcsinIntegralSeries
  have hzero : (fun n : ℕ => centralBinomialCoeff n * (0 : ℝ) ^ (2 * n + 1) /
      ((2 * n + 1 : ℕ) : ℝ) ^ 2) = fun _ => 0 := by
    funext n
    have hz : (0 : ℝ) ^ (2 * n + 1) = 0 := zero_pow (by omega)
    rw [hz]
    simp
  rw [hzero, tsum_zero]

/-- **Continuity of the integrated arcsine series.** The integrated arcsine series
$F(t) = \sum_{n \ge 0} \binom{2n}{n} 4^{-n}\, t^{2n+1}/(2n+1)^2$ is continuous on the closed
interval $[-1, 1]$. -/
theorem continuousOn_arcsinIntegralSeries :
    ContinuousOn arcsinIntegralSeries (Set.Icc (-1 : ℝ) 1) := by
  apply continuousOn_tsum (fun n => ?_) summable_one_div_nat_add_one_sq (fun n x hx => ?_)
  · apply ContinuousOn.div_const
    apply ContinuousOn.mul continuousOn_const
    exact (continuous_pow (2 * n + 1)).continuousOn
  · have ht : ‖x‖ ≤ 1 := by
      rw [Set.mem_Icc] at hx
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hx.1, hx.2]
    exact norm_arcsinIntegralSeries_term_le x ht n

private lemma one_div_odd_le_one (n : ℕ) : (1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ) ≤ 1 := by
  have h1 : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    have hle : 1 ≤ 2 * n + 1 := by omega
    exact_mod_cast hle
  calc (1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ) ≤ 1 / 1 := by
        apply one_div_le_one_div_of_le (by norm_num) h1
      _ = 1 := by simp

private lemma arcsinIntegralSeries_deriv_majorant
    (r : ℝ) (_hr0 : 0 < r) (_hr1 : r < 1) (n : ℕ) (y : ℝ)
    (hy : y ∈ Set.Ioo (-r) r) :
    ‖centralBinomialCoeff n * y ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ)‖ ≤ (r ^ 2) ^ n := by
  have hyr : ‖y‖ < r := by
    rw [Real.norm_eq_abs]
    rw [Set.mem_Ioo] at hy
    rw [abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hc : ‖centralBinomialCoeff n‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (centralBinomialCoeff_nonneg n)]
    exact centralBinomialCoeff_le_one n
  have hd : ‖(1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact one_div_odd_le_one n
  have hpow_le : ‖y‖ ^ (2 * n) ≤ r ^ (2 * n) :=
    pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hyr) _
  have h1 : ‖centralBinomialCoeff n‖ * ‖y‖ ^ (2 * n) ≤ 1 * r ^ (2 * n) :=
    mul_le_mul hc hpow_le (by positivity) (by norm_num)
  have h2 : (‖centralBinomialCoeff n‖ * ‖y‖ ^ (2 * n)) * ‖(1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ)‖ ≤
      (1 * r ^ (2 * n)) * 1 :=
    mul_le_mul h1 hd (by positivity) (by positivity)
  have heq : ‖centralBinomialCoeff n * y ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ)‖
      = (‖centralBinomialCoeff n‖ * ‖y‖ ^ (2 * n)) * ‖(1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ)‖ := by
    rw [div_eq_mul_one_div]
    simp [norm_mul, norm_pow, mul_assoc]
  rw [heq]
  calc (‖centralBinomialCoeff n‖ * ‖y‖ ^ (2 * n)) * ‖1 / ((2 * n + 1 : ℕ) : ℝ)‖
        ≤ (1 * r ^ (2 * n)) * 1 := h2
      _ = (r ^ 2) ^ n := by ring

private lemma arcsinIntegralSeries_hasDerivAt_of_mem {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hy : y ∈ Set.Ioo (-r) r) :
    HasDerivAt arcsinIntegralSeries
      (∑' n : ℕ, centralBinomialCoeff n * y ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ)) y := by
  have hu : Summable (fun n : ℕ => (r ^ 2) ^ n) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hr0, hr1]
  have hopen : IsOpen (Set.Ioo (-r : ℝ) r) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (-r : ℝ) r) := isPreconnected_Ioo
  have hderiv : ∀ n : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      HasDerivAt (fun s : ℝ => centralBinomialCoeff n * s ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ^ 2)
        (centralBinomialCoeff n * z ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ)) z :=
    fun n z _ => arcsinIntegralSeries_term_hasDerivAt n z
  have hbound : ∀ n : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      ‖centralBinomialCoeff n * z ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ)‖ ≤ (r ^ 2) ^ n :=
    fun n z hz => arcsinIntegralSeries_deriv_majorant r hr0 hr1 n z hz
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-r : ℝ) r := by simp [Set.mem_Ioo, hr0]
  have hsum0 : Summable (fun n : ℕ => centralBinomialCoeff n * (0 : ℝ) ^ (2 * n + 1) /
      ((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
    apply Summable.of_norm
    have hle : ∀ n : ℕ,
        ‖centralBinomialCoeff n * (0 : ℝ) ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ^ 2‖ ≤
          (1 : ℝ) / (((n : ℝ) + 1) ^ 2) := by
      intro n
      have h0 : ‖(0 : ℝ)‖ ≤ 1 := by simp
      exact norm_arcsinIntegralSeries_term_le 0 h0 n
    exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle summable_one_div_nat_add_one_sq
  exact hasDerivAt_tsum_of_isPreconnected hu hopen hpre hderiv hbound hy0 hsum0 hy

private lemma norm_lt_one_mem_Ioo (y : ℝ) (hy : ‖y‖ < 1) : y ∈ Set.Ioo (-1 : ℝ) 1 := by
  rw [Real.norm_eq_abs, abs_lt] at hy
  rw [Set.mem_Ioo]
  constructor <;> linarith [hy.1, hy.2]

/-- **Summability of the arcsine series.** Write $c_n = \binom{2n}{n}/4^n$ for the normalized
central binomial coefficient. For every real number $y$ with $|y| < 1$, the series
$\sum_{n=0}^{\infty} \frac{c_n\, y^{2n+1}}{2n+1}$ converges absolutely. -/
theorem summable_arcsinSeries_term {y : ℝ} (hy : ‖y‖ < 1) :
    Summable (fun n : ℕ => centralBinomialCoeff n * y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) := by
  have hr1 : (‖y‖ + 1) / 2 < 1 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith [hy]
  have hr0 : (0 : ℝ) < (‖y‖ + 1) / 2 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith
  have hr : ‖y‖ < (‖y‖ + 1) / 2 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith [hy]
  have hu : Summable (fun n : ℕ => ((((‖y‖ + 1) / 2) ^ 2) ^ n)) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hr0, hr1]
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hu
  have hyr : ‖y‖ < (‖y‖ + 1) / 2 := hr
  have hc : ‖centralBinomialCoeff n‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (centralBinomialCoeff_nonneg n)]
    exact centralBinomialCoeff_le_one n
  have hd : ‖(1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact one_div_odd_le_one n
  have hpow : ‖y‖ ^ (2 * n + 1) ≤ ((‖y‖ + 1) / 2) ^ (2 * n + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hyr) _
  have hpow2 : ((‖y‖ + 1) / 2) ^ (2 * n + 1) ≤ ((‖y‖ + 1) / 2) ^ (2 * n) := by
    have hrr : ((‖y‖ + 1) / 2) ^ (2 * n) * ((‖y‖ + 1) / 2) ≤
        ((‖y‖ + 1) / 2) ^ (2 * n) * 1 :=
      mul_le_mul_of_nonneg_left (le_of_lt hr1) (by positivity)
    rwa [← pow_succ, mul_one] at hrr
  calc ‖centralBinomialCoeff n * y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)‖
        = (‖centralBinomialCoeff n‖ * ‖y‖ ^ (2 * n + 1)) * ‖(1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ)‖ := by
          rw [div_eq_mul_one_div]
          simp [norm_mul, norm_pow, mul_assoc]
      _ ≤ (1 * ((‖y‖ + 1) / 2) ^ (2 * n + 1)) * 1 := by
          have h1 : ‖centralBinomialCoeff n‖ * ‖y‖ ^ (2 * n + 1) ≤
              1 * ((‖y‖ + 1) / 2) ^ (2 * n + 1) :=
            mul_le_mul hc hpow (by positivity) (by norm_num)
          exact mul_le_mul h1 hd (by positivity) (by positivity)
      _ ≤ ((((‖y‖ + 1) / 2) ^ 2) ^ n) := by
          calc (1 * ((‖y‖ + 1) / 2) ^ (2 * n + 1)) * 1
                = ((‖y‖ + 1) / 2) ^ (2 * n + 1) := by ring
            _ ≤ ((‖y‖ + 1) / 2) ^ (2 * n) := hpow2
            _ = ((((‖y‖ + 1) / 2) ^ 2) ^ n) := by
              exact pow_mul _ 2 n

/-- **Derivative of the integrated arcsine series.** Let
$F(t) = \sum_{n \ge 0} \binom{2n}{n} 4^{-n}\, t^{2n+1}/(2n+1)^2$ be the integrated arcsine
series. For every real $y$ with $|y| < 1$ and $y \neq 0$, $F$ is differentiable at $y$ with
$F'(y) = \arcsin(y)/y$. -/
theorem hasDerivAt_arcsinIntegralSeries {y : ℝ} (hy : ‖y‖ < 1) (hy0 : y ≠ 0) :
    HasDerivAt arcsinIntegralSeries (Real.arcsin y / y) y := by
  have hr1 : (‖y‖ + 1) / 2 < 1 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith [hy]
  have hr0 : (0 : ℝ) < (‖y‖ + 1) / 2 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith
  have habs : |y| < (‖y‖ + 1) / 2 := by
    rw [← Real.norm_eq_abs]
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith [hy]
  rw [abs_lt] at habs
  have hymem : y ∈ Set.Ioo (-((‖y‖ + 1) / 2)) ((‖y‖ + 1) / 2) := by
    rw [Set.mem_Ioo]
    constructor <;> linarith [habs.1, habs.2]
  have hF := arcsinIntegralSeries_hasDerivAt_of_mem hr0 hr1 hymem
  have hGsum := summable_arcsinSeries_term hy
  have hterm :
      (fun n : ℕ => centralBinomialCoeff n * y ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ)) =
        (fun n : ℕ =>
          (centralBinomialCoeff n * y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) * y⁻¹) := by
    funext n
    have hne : ((2 * n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt (by positivity)
    have hpow : y ^ (2 * n + 1) = y ^ (2 * n) * y := by
      rw [show 2 * n + 1 = (2 * n) + 1 by ring, pow_succ]
    rw [hpow]
    field_simp
  have hsum_eq : (∑' n : ℕ, centralBinomialCoeff n * y ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ))
      = (∑' n : ℕ, centralBinomialCoeff n * y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) / y := by
    rw [hterm, hGsum.tsum_mul_right, div_eq_mul_inv]
  have hGval : (∑' n : ℕ, centralBinomialCoeff n * y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ))
      = Real.arcsin y := by
    have heq : arcsinSeries y = Real.arcsin y :=
      arcsinSeries_eq_arcsin (norm_lt_one_mem_Ioo y hy)
    unfold arcsinSeries at heq
    exact heq
  rw [hsum_eq, hGval] at hF
  exact hF


end

end MathlibExt.Analysis.SpecialFunctions.ArcsinTaylorSeries
