/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.PrimeCounting
public import MathlibExt.Analysis.SpecialFunctions.Log.IntegralDerivative
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Axler's bounds for prime counting

The convolution defining the reciprocal coefficients cancels all positive degrees through
the truncation order. The remaining terms in the product have nonpositive coefficients.

The bounds by the auxiliary functions $J$ follow from Abel summation and a two-sided
estimate for Chebyshev's theta function.

The last branch of the error factor becomes $C u^{15} e^{-2u}$ after the substitution
$u = \sqrt{\log y / R}$. The ratio of two values is controlled by $1 + t \le e^t$, so the
function decreases for $u \ge 15/2$.

The tail $\sum_{p > x} p^{-n}$ over the primes $p > x$ is compared with
$-\operatorname{li}(x^{1-n})$, the integral of $1 / (t^n \log t)$ over $(x, \infty)$. On a finite
interval $(x, N]$, Abel summation against $\vartheta(t) - t$ bounds their difference, and the
bound passes to the limit $N \to \infty$ because $\operatorname{li}(y) \to 0$ as $y \to 0^+$.
-/

namespace MetaMathlibExt

open Finset

-- The pairs with i + j ≤ n form a subset of the rectangle in the product of the sums.
private theorem sum_truncated_convolution_le (n : ℕ) (u v : ℕ → ℝ)
    (hu : ∀ i ∈ Icc 1 n, 0 ≤ u i) (hv : ∀ j ≤ n, 0 ≤ v j) :
    (∑ k ∈ Icc 1 n, ∑ i ∈ Icc 1 k, u i * v (k - i)) ≤
      (∑ i ∈ Icc 1 n, u i) * ∑ j ∈ range (n + 1), v j := by
  simp_rw [← Ico_add_one_right_eq_Icc]
  rw [← sum_Ico_Ico_comm 1 (n + 1) (fun i k ↦ u i * v (k - i)), sum_mul]
  refine sum_le_sum fun i hi ↦ ?_
  rw [sum_Ico_eq_sum_range, ← mul_sum]
  simp only [Nat.add_sub_cancel_left]
  apply mul_le_mul_of_nonneg_left _ (hu i (by simpa using hi))
  exact sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le _ _))
    fun j hj _ ↦ hv j (by simpa using hj)

/-- **Converting a lower bound for $\pi(x)$ into a truncated series.** Let $\pi(x)$ be the number
of primes $p \le x$. Let $n \ge 1$ be an integer, let $a_0, \dots, a_n$ be reals with $a_0 > 0$
and $a_1, \dots, a_n < 0$, and let $x_0 > 0$. Suppose that for every real $x \ge x_0$ the
denominator $D(x) = a_0 \log x + \sum_{i=1}^{n} a_i / \log^{i-1} x$ is positive and
$\pi(x) > x / D(x)$. Let $b_0 = 1/a_0$ and $b_k = -\frac{1}{a_0} \sum_{i=1}^{k} a_i b_{k-i}$ for
$1 \le k \le n$. Then for every real $x \ge x_0$,
$\pi(x) > \sum_{k=0}^{n} \frac{b_k x}{\log^{k+1} x}$.

The recursion uses $b_{k-i}$, the index of the paper's proof: it turns the first row of Table 5
into the Table 6 coefficients $1, 1, 2, 5.975666, 23.975666, \dots$. The source record of the
statement prints $b_{k-1}$ instead, which would give $b_3 = 9.951332$ there.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Proposition 6 (`integers-2024-A34-prop-6`). -/
public theorem series_lt_primeCounting_of_lt_primeCounting (n : ℕ) (hn : 1 ≤ n)
    (a b : ℕ → ℝ) (ha₀ : 0 < a 0) (ha : ∀ i ∈ Finset.Icc 1 n, a i < 0) (x₀ : ℝ) (hx₀ : 0 < x₀)
    (hpos : ∀ x : ℝ, x₀ ≤ x →
      0 < a 0 * Real.log x + ∑ i ∈ Finset.Icc 1 n, a i / Real.log x ^ (i - 1))
    (hlow : ∀ x : ℝ, x₀ ≤ x →
      x / (a 0 * Real.log x + ∑ i ∈ Finset.Icc 1 n, a i / Real.log x ^ (i - 1)) <
        (Nat.primeCounting ⌊x⌋₊ : ℝ))
    (hb₀ : b 0 = 1 / a 0)
    (hb : ∀ k ∈ Finset.Icc 1 n, b k = -(1 / a 0) * ∑ i ∈ Finset.Icc 1 k, a i * b (k - i))
    (x : ℝ) (hx : x₀ ≤ x) :
    ∑ k ∈ Finset.range (n + 1), b k * x / Real.log x ^ (k + 1) <
      (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hx₀' : 1 < x₀ := by
    by_contra! h
    have h₁ := (div_pos zero_lt_one (hpos 1 h)).trans (hlow 1 h)
    simp at h₁
  have hlog := Real.log_pos (hx₀'.trans_le hx)
  let u (i : ℕ) := -(a i / Real.log x ^ (i - 1))
  let v (k : ℕ) := b k * x / Real.log x ^ (k + 1)
  have hu (i : ℕ) (hi : i ∈ Icc 1 n) : 0 ≤ u i :=
    neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg (ha i hi).le (pow_nonneg hlog.le _))
  have hv₀ : a 0 * Real.log x * v 0 = x := by
    dsimp [v]
    rw [hb₀]
    field_simp
  have hrec (k : ℕ) (hk : k ∈ Icc 1 n) :
      a 0 * Real.log x * v k = ∑ i ∈ Icc 1 k, u i * v (k - i) := by
    calc
      a 0 * Real.log x * v k =
          (∑ i ∈ Icc 1 k, a i * b (k - i)) * (-x / Real.log x ^ k) := by
        dsimp [v]
        rw [hb k hk, pow_succ]
        field_simp
      _ = _ := by
        rw [sum_mul]
        refine sum_congr rfl fun i hi ↦ ?_
        obtain ⟨hi₁, hik⟩ := mem_Icc.mp hi
        dsimp [u, v]
        rw [← neg_div, div_mul_div_comm, ← pow_add,
          show i - 1 + (k - i + 1) = k by omega]
        ring
  have hv (k : ℕ) : k ≤ n → 0 ≤ v k := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk
      apply nonneg_of_mul_nonneg_right (a := a 0 * Real.log x) _ (mul_pos ha₀ hlog)
      cases k with
      | zero => simpa only [hv₀] using (hx₀.trans_le hx).le
      | succ k =>
        rw [hrec _ (mem_Icc.mpr ⟨by omega, hk⟩)]
        refine sum_nonneg fun i hi ↦ ?_
        obtain ⟨hi₁, hik⟩ := mem_Icc.mp hi
        exact mul_nonneg (hu _ (mem_Icc.mpr ⟨hi₁, hik.trans hk⟩))
          (ih _ (by omega) (by omega))
  have htrunc := sum_truncated_convolution_le n u v hu hv
  have hsplit : a 0 * Real.log x * (∑ k ∈ range (n + 1), v k) =
      x + ∑ k ∈ Icc 1 n, ∑ i ∈ Icc 1 k, u i * v (k - i) := by
    rw [mul_sum, sum_range_eq_add_Ico _ (hn.trans (Nat.le_add_right n 1)), hv₀,
      Ico_add_one_right_eq_Icc]
    exact congrArg (x + ·) (sum_congr rfl hrec)
  apply lt_of_le_of_lt _ (hlow x hx)
  apply (le_div_iff₀ (hpos x hx)).mpr
  change (∑ k ∈ range (n + 1), v k) * _ ≤ x
  have hden : ∑ i ∈ Icc 1 n, u i = -(∑ i ∈ Icc 1 n, a i / Real.log x ^ (i - 1)) := by
    simp [u]
  rw [hden] at htrunc
  linarith only [hsplit, htrunc]

open MeasureTheory Real

namespace primeCounting_mem_Icc_auxJ

-- Extend Abel summation below the first prime. The jump of theta at 2 contributes
-- nothing to the integral over an interval ending there.
private theorem primeCounting_eq_theta_integral (x : ℝ) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) =
      Chebyshev.theta x / log x + ∫ t in 2..x, Chebyshev.theta t / (t * log t ^ 2) := by
  rcases le_or_gt 2 x with hx | hx
  · exact Chebyshev.primeCounting_eq_theta_div_log_add_integral hx
  have hfloor : ⌊x⌋₊ < 2 := (Nat.floor_lt' (by decide : 2 ≠ 0)).2 (by simpa using hx)
  rw [Nat.primeCounting_eq_zero_iff.mpr (by omega), Chebyshev.theta_eq_zero_of_lt_two hx,
    intervalIntegral.integral_symm]
  have hzero := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) hx.le
    (f := fun t ↦ Chebyshev.theta t / (t * log t ^ 2)) (g := fun _ ↦ 0)
    (fun t ht ↦ by simp [Chebyshev.theta_eq_zero_of_lt_two ht.2])
  simp [hzero]

private theorem intervalIntegrable_theta_div {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t ↦ Chebyshev.theta t / (t * log t ^ 2)) volume a b := by
  simp only [div_eq_mul_inv]
  apply Chebyshev.theta_mono.intervalIntegrable.mul_continuousOn
  intro t ht
  have ht₁ : 1 < t := (lt_min ha hb).trans_le ht.1
  have ht₀ : 0 < t := zero_lt_one.trans ht₁
  have hlog := log_pos ht₁
  fun_prop (disch := positivity)

end primeCounting_mem_Icc_auxJ

open primeCounting_mem_Icc_auxJ in
-- The comparison uses only the error bound, independently of the positivity of k and η.
set_option linter.unusedVariables false in
/-- **Prime counting between the auxiliary functions $J$.** Let $\pi(x)$ be the number of primes
$p \le x$ and $\vartheta(x) = \sum_{p \le x} \log p$ Chebyshev's function. Let $k \ge 1$ be an
integer and let $\eta > 0$ and $x_1 > 1$ be reals with $|\vartheta(y) - y| < \eta y / \log^k y$
for every real $y \ge x_1$. For reals $e$ and $x \ge x_1$ set
$J_e(x) = \pi(x_1) - \frac{\vartheta(x_1)}{\log x_1} + \frac{x}{\log x} +
\frac{e\,x}{\log^{k+1} x} + \int_{x_1}^{x} \left(\frac{1}{\log^2 t} +
\frac{e}{\log^{k+2} t}\right) dt$.
Then $J_{-\eta}(x) \le \pi(x) \le J_{\eta}(x)$ for every real $x \ge x_1$.

The inequalities are non-strict, as the paper prints them.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Lemma 1 (`integers-2024-A34-lem-1`). -/
public theorem primeCounting_mem_Icc_auxJ (k : ℕ) (hk : 0 < k) (η x₁ : ℝ) (hη : 0 < η)
    (hx₁ : 1 < x₁)
    (hθ : ∀ y : ℝ, x₁ ≤ y → |Chebyshev.theta y - y| < η * y / Real.log y ^ k)
    (x : ℝ) (hx : x₁ ≤ x) :
    let J : ℝ → ℝ := fun e =>
      (Nat.primeCounting ⌊x₁⌋₊ : ℝ) - Chebyshev.theta x₁ / Real.log x₁ + x / Real.log x +
        e * x / Real.log x ^ (k + 1) +
          ∫ t in x₁..x, (1 / Real.log t ^ 2 + e / Real.log t ^ (k + 2))
    J (-η) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ J η := by
  intro J
  -- F evaluates the endpoint and integral terms of Abel summation on a given function.
  let B (e t : ℝ) := t + e * t / log t ^ k
  let F (f : ℝ → ℝ) :=
    (Nat.primeCounting ⌊x₁⌋₊ : ℝ) - Chebyshev.theta x₁ / log x₁ + f x / log x +
      ∫ t in x₁..x, f t / (t * log t ^ 2)
  have hx' := hx₁.trans_le hx
  have hπ : F Chebyshev.theta = (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
    dsimp [F]
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_theta_div one_lt_two hx₁) (intervalIntegrable_theta_div hx₁ hx')
    linarith only [primeCounting_eq_theta_integral x, primeCounting_eq_theta_integral x₁, hadd]
  have hJ (e : ℝ) : J e = F (B e) := by
    have hend : B e x / log x = x / log x + e * x / log x ^ (k + 1) := by
      dsimp only [B]
      rw [add_div, div_div, pow_succ]
    have hint (t : ℝ) (ht : t ∈ Set.uIcc x₁ x) :
        B e t / (t * log t ^ 2) = 1 / log t ^ 2 + e / log t ^ (k + 2) := by
      have ht₁ := hx₁.trans_le ((Set.uIcc_of_le hx ▸ ht).1)
      have ht₀ := zero_lt_one.trans ht₁
      have hlog := log_pos ht₁
      dsimp [B]
      rw [pow_add]
      field_simp
    dsimp only [F, J]
    rw [hend, intervalIntegral.integral_congr hint]
    ring
  have hmono {f g : ℝ → ℝ}
      (hf : IntervalIntegrable (fun t ↦ f t / (t * log t ^ 2)) volume x₁ x)
      (hg : IntervalIntegrable (fun t ↦ g t / (t * log t ^ 2)) volume x₁ x)
      (hfg : ∀ t ∈ Set.Icc x₁ x, f t ≤ g t) : F f ≤ F g := by
    dsimp only [F]
    have hend := div_le_div_of_nonneg_right (hfg x ⟨hx, le_rfl⟩) (log_pos hx').le
    refine add_le_add (add_le_add_right hend _) (intervalIntegral.integral_mono_on hx hf hg ?_)
    intro t ht
    exact div_le_div_of_nonneg_right (hfg t ht)
      (mul_nonneg (zero_lt_one.trans (hx₁.trans_le ht.1)).le (sq_nonneg _))
  have hB (e : ℝ) : IntervalIntegrable (fun t ↦ B e t / (t * log t ^ 2)) volume x₁ x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht₁ := hx₁.trans_le ((Set.uIcc_of_le hx ▸ ht).1)
    have ht₀ := zero_lt_one.trans ht₁
    have hlog := log_pos ht₁
    dsimp only [B]
    fun_prop (disch := positivity)
  have hbounds (t : ℝ) (ht : x₁ ≤ t) :
      B (-η) t ≤ Chebyshev.theta t ∧ Chebyshev.theta t ≤ B η t := by
    obtain ⟨hlo, hhi⟩ := abs_lt.mp (hθ t ht)
    dsimp [B]
    rw [neg_mul, neg_div]
    constructor <;> linarith
  rw [hJ, hJ, ← hπ]
  exact ⟨hmono (hB _) (intervalIntegrable_theta_div hx₁ hx') (fun t ht ↦ (hbounds t ht.1).1),
    hmono (intervalIntegrable_theta_div hx₁ hx') (hB _) (fun t ht ↦ (hbounds t ht.1).2)⟩

namespace axlerThetaErrorFactor_tail_antitone

-- For `15 / 2 ≤ u ≤ v` we have `(v / u) ^ 15 ≤ exp (15 (v - u) / u) ≤ exp (2 (v - u))`.
private theorem pow_mul_exp_neg_antitone {u v : ℝ} (hu : 15 / 2 ≤ u) (huv : u ≤ v) :
    v ^ 15 * exp (-2 * v) ≤ u ^ 15 * exp (-2 * u) := by
  have hu₀ : 0 < u := by linarith
  have hratio : v / u ≤ exp ((v - u) / u) := by
    have h := add_one_le_exp ((v - u) / u)
    rwa [div_add_one hu₀.ne', sub_add_cancel] at h
  have hpow : (v / u) ^ 15 ≤ exp (2 * (v - u)) := by
    calc (v / u) ^ 15 ≤ exp ((v - u) / u) ^ 15 :=
          pow_le_pow_left₀ (div_nonneg (hu₀.le.trans huv) hu₀.le) hratio 15
      _ = exp (15 * ((v - u) / u)) := by rw [← exp_nat_mul]; norm_num
      _ ≤ exp (2 * (v - u)) := by
          refine exp_le_exp.mpr ?_
          rw [mul_div_assoc', div_le_iff₀ hu₀]
          nlinarith
  calc v ^ 15 * exp (-2 * v) = u ^ 15 * (v / u) ^ 15 * exp (-2 * v) := by
        rw [div_pow]
        field_simp
    _ ≤ u ^ 15 * exp (2 * (v - u)) * exp (-2 * v) := by gcongr
    _ = u ^ 15 * exp (-2 * u) := by
        rw [mul_assoc, ← exp_add]
        congr 2
        ring

-- With `u = √(L / R)` we have `L = R u ^ 2` and `(L / R) ^ (3 / 2) = u ^ 3`.
private theorem eq_mul_pow_mul_exp {L : ℝ} (hL : 0 ≤ L) :
    L ^ 6 * (121.0961 * (L / 5.5666305) ^ (3 / 2 : ℝ) * exp (-2 * √(L / 5.5666305))) =
      121.0961 * 5.5666305 ^ 6 * (√(L / 5.5666305) ^ 15 * exp (-2 * √(L / 5.5666305))) := by
  have hLR : 0 ≤ L / 5.5666305 := div_nonneg hL (by norm_num)
  have h32 : (L / 5.5666305) ^ (3 / 2 : ℝ) = √(L / 5.5666305) ^ 3 := by
    rw [sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul hLR]
    norm_num
  have hL' : L = 5.5666305 * √(L / 5.5666305) ^ 2 := by
    rw [sq_sqrt hLR]
    field_simp
  rw [h32]
  generalize √(L / 5.5666305) = u at hL' ⊢
  subst hL'
  ring

end axlerThetaErrorFactor_tail_antitone

open axlerThetaErrorFactor_tail_antitone in
/-- **The last branch of Axler's error factor is nonincreasing.** Let $R = 5.5666305$ and for
real $y \ge e^{673}$ let
$$
a(y) = \log^6 y \cdot 121.0961 \Big(\frac{\log y}{R}\Big)^{3/2}
\exp\Big(-2\sqrt{\frac{\log y}{R}}\Big).
$$
Then $a(x) \le a(x_1)$ for all reals $x_1$ and $x$ with $e^{673} \le x_1 \le x$.

This is the paper's function $a$ on $y \ge e^{673}$. The paper prints the statement as
$a_n(x) \le a_n(x_1)$; its proof ($a'(x) < 0$ for $x \ge e^{673}$) and the later use
$a(t) \le a(x_1)$ show that $a_n$ is a typo for $a$.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Lemma 5 (`integers-2024-A34-lem-5`), with the function `a`
defined at the start of Section 6. -/
public theorem axlerThetaErrorFactor_tail_antitone (x₁ x : ℝ)
    (hx₁ : Real.exp 673 ≤ x₁) (hx : x₁ ≤ x) :
    Real.log x ^ 6 * (121.0961 * (Real.log x / 5.5666305) ^ (3 / 2 : ℝ) *
        Real.exp (-2 * Real.sqrt (Real.log x / 5.5666305))) ≤
      Real.log x₁ ^ 6 * (121.0961 * (Real.log x₁ / 5.5666305) ^ (3 / 2 : ℝ) *
        Real.exp (-2 * Real.sqrt (Real.log x₁ / 5.5666305))) := by
  have hx₁₀ : 0 < x₁ := (exp_pos 673).trans_le hx₁
  have hL₁ : 673 ≤ log x₁ := (le_log_iff_exp_le hx₁₀).mpr hx₁
  have hL : log x₁ ≤ log x := log_le_log hx₁₀ hx
  rw [eq_mul_pow_mul_exp (by linarith), eq_mul_pow_mul_exp (by linarith)]
  refine mul_le_mul_of_nonneg_left (pow_mul_exp_neg_antitone ?_ ?_) (by norm_num)
  · -- `(15 / 2) ^ 2 * R < 314 < 673`.
    rw [le_sqrt (by norm_num) (div_nonneg (by linarith) (by norm_num)),
      le_div_iff₀ (by norm_num)]
    linarith
  · exact sqrt_le_sqrt (div_le_div_of_nonneg_right hL (by norm_num))

section

open Filter Topology

namespace abs_logarithmicIntegral_add_tsum_inv_prime_pow_lt

-- The weight `1 / (t ^ n log t)` of Abel summation and its derivative.
private theorem hasDerivAt_weight {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t : ℝ ↦ 1 / (t ^ n * log t))
      (-(n * log t + 1) / (t ^ (n + 1) * log t ^ 2)) t := by
  have ht₀ : 0 < t := zero_lt_one.trans ht
  have hlog := log_pos ht
  have h := ((hasDerivAt_pow n t).fun_mul (hasDerivAt_log ht₀.ne')).fun_inv
    (by positivity : t ^ n * log t ≠ 0)
  convert h using 1
  · ext s
    simp [one_div]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    field_simp
    ring

-- The derivative of `t ↦ li(t ^ (1 - n))` is the weight.
private theorem hasDerivAt_logarithmicIntegralReal_rpow {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht : 1 < t) :
    HasDerivAt (fun t : ℝ ↦ logarithmicIntegralReal (t ^ ((1 : ℝ) - n)))
      (1 / (t ^ n * log t)) t := by
  have ht₀ : 0 < t := zero_lt_one.trans ht
  have hlog := log_pos ht
  have hn' : (1 : ℝ) - n < 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hli := hasDerivAt_logarithmicIntegralReal (rpow_pos_of_pos ht₀ ((1 : ℝ) - n))
    (rpow_lt_one_of_one_lt_of_neg ht hn').ne
  have h := hli.comp t (hasDerivAt_rpow_const (p := (1 : ℝ) - n) (Or.inl ht₀.ne'))
  convert h using 1
  · rfl
  · rw [log_rpow ht₀, show (1 : ℝ) - n - 1 = -(n : ℝ) by ring, rpow_neg ht₀.le, rpow_natCast]
    have := hn'.ne
    field_simp

-- On `(0, 1/2]` the integrand `1 / log t` of `li` is bounded by `1 / log 2`.
private theorem abs_logarithmicIntegralReal_le {y : ℝ} (hy₀ : 0 ≤ y) (hy : y ≤ 1 / 2) :
    |logarithmicIntegralReal y| ≤ y / log 2 := by
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  rw [logarithmicIntegralReal_of_lt_one hy₀ (by linarith)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := y)
    (f := fun t ↦ (log t)⁻¹) (C := (log 2)⁻¹) fun t ht ↦ by
      rw [Set.uIoc_of_le hy₀] at ht
      have hle : log t ≤ log 2⁻¹ := log_le_log ht.1 (by linarith [ht.2])
      rw [log_inv] at hle
      rw [norm_inv, Real.norm_eq_abs, abs_of_neg (by linarith)]
      exact inv_anti₀ hlog2 (by linarith)
  simpa [abs_of_nonneg hy₀, div_eq_inv_mul] using h

-- `li(N ^ (1 - n)) → 0` as `N → ∞`, since `N ^ (1 - n) → 0`.
private theorem tendsto_logarithmicIntegralReal_rpow {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun N : ℕ ↦ logarithmicIntegralReal ((N : ℝ) ^ ((1 : ℝ) - n))) atTop (𝓝 0) := by
  have hn' : 0 < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hy : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ ((1 : ℝ) - n)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop hn').comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, neg_sub] using this
  refine squeeze_zero_norm' ?_ (by simpa using hy.div_const (log 2))
  filter_upwards [(tendsto_order.1 hy).2 (1 / 2) (by norm_num)] with N hN
  rw [Real.norm_eq_abs]
  exact abs_logarithmicIntegralReal_le (rpow_nonneg (Nat.cast_nonneg N) _) hN.le

-- The partial sums of the tail as sums over `(⌊x⌋, N]` weighted by `log p`.
private theorem sum_range_eq_sum_Ioc (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    ∑ p ∈ range (N + 1), (if p.Prime ∧ x < p then 1 / (p : ℝ) ^ n else 0) =
      ∑ i ∈ Ioc ⌊x⌋₊ N, 1 / ((i : ℝ) ^ n * log i) * (if i.Prime then log i else 0) := by
  have hIoc : Ioc ⌊x⌋₊ N = (range (N + 1)).filter (fun i ↦ ⌊x⌋₊ < i) := by
    ext i
    simp only [mem_Ioc, mem_filter, mem_range]
    omega
  rw [hIoc, sum_filter]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [Nat.floor_lt hx]
  by_cases hp : i.Prime
  · have hlog : log i ≠ 0 := (log_pos (by exact_mod_cast hp.one_lt)).ne'
    by_cases hxi : x < i
    · simp only [hp, hxi, and_self, ↓reduceIte]
      field_simp
    · simp only [hp, hxi, and_false, ↓reduceIte]
  · simp [hp]

-- An antiderivative of the majorant of the integrand.
private theorem hasDerivAt_majorant (k : ℕ) {n : ℕ} (hn : 2 ≤ n) (η : ℝ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t : ℝ ↦ -(η * n / ((n : ℝ) - 1)) / (t ^ (n - 1) * log t ^ (k + 1)))
      (η / (t ^ n * log t ^ (k + 2)) * (n * log t + n * (k + 1) / ((n : ℝ) - 1))) t := by
  have ht₀ : 0 < t := zero_lt_one.trans ht
  have hlog := log_pos ht
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hD := (hasDerivAt_pow (m + 1) t).fun_mul ((hasDerivAt_log ht₀.ne').fun_pow (k + 1))
  have h := (hD.fun_inv (by positivity : t ^ (m + 1) * log t ^ (k + 1) ≠ 0)).const_mul
    (-(η * ((m + 2 : ℕ) : ℝ) / (((m + 2 : ℕ) : ℝ) - 1)))
  convert h using 1
  · ext s
    simp [div_eq_mul_inv]
  · rw [show ((m + 2 : ℕ) : ℝ) - 1 = (m : ℝ) + 1 by push_cast; ring]
    simp only [Nat.add_sub_cancel]
    push_cast
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

-- The weight times the error bound `η t / log^k t` of the endpoint terms.
private theorem weight_mul_eq (k : ℕ) {n : ℕ} (hn : 1 ≤ n) (η : ℝ) {t : ℝ} (ht : 1 < t) :
    1 / (t ^ n * log t) * (η * t / log t ^ k) = η / (t ^ (n - 1) * log t ^ (k + 1)) := by
  have ht₀ : 0 < t := zero_lt_one.trans ht
  have hlog := log_pos ht
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

-- The difference between the partial sum over `(x, b]` and its integral, by Abel summation.
private theorem abs_partial_sub_le (k : ℕ) (η x₀ : ℝ) (hη : 0 < η)
    (hθ : ∀ y : ℝ, x₀ ≤ y → |Chebyshev.theta y - y| < η * y / log y ^ k)
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx₁ : 1 < x) (hx : x₀ ≤ x) {b : ℝ} (hxb : x ≤ b) :
    |logarithmicIntegralReal (x ^ ((1 : ℝ) - n)) +
        ∑ i ∈ Ioc ⌊x⌋₊ ⌊b⌋₊, 1 / ((i : ℝ) ^ n * log i) * (if i.Prime then log i else 0) -
        logarithmicIntegralReal (b ^ ((1 : ℝ) - n))| ≤
      1 / (x ^ n * log x) * |Chebyshev.theta x - x| +
        η * n / ((n : ℝ) - 1) / (x ^ (n - 1) * log x ^ (k + 1)) := by
  have hb₁ : 1 < b := hx₁.trans_le hxb
  have hn₁ : (0 : ℝ) < n - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set L : ℝ → ℝ := fun t ↦ logarithmicIntegralReal (t ^ ((1 : ℝ) - n))
  set f : ℝ → ℝ := fun t ↦ 1 / (t ^ n * log t) with hf
  set f' : ℝ → ℝ := fun t ↦ -(n * log t + 1) / (t ^ (n + 1) * log t ^ 2) with hf'
  set c : ℕ → ℝ := fun i ↦ if i.Prime then log i else 0
  set A : ℝ := η * n / ((n : ℝ) - 1) with hA
  have hmem : ∀ t ∈ Set.uIcc x b, 1 < t := fun t ht ↦
    hx₁.trans_le (Set.uIcc_of_le hxb ▸ ht).1
  have hfd : ∀ t, 1 < t → HasDerivAt f (f' t) t := fun t ht ↦ hasDerivAt_weight (by omega) ht
  have hf'c : ContinuousOn f' (Set.uIcc x b) := by
    intro t ht
    have ht₁ := hmem t ht
    have ht₀ : 0 < t := zero_lt_one.trans ht₁
    have hlog := log_pos ht₁
    exact ContinuousAt.continuousWithinAt (by simp only [hf']; fun_prop (disch := positivity))
  -- Abel summation against `θ`.
  have habel := sum_mul_eq_sub_sub_integral_mul c (f := f) (zero_lt_one.trans hx₁).le hxb
    (fun t ht ↦ (hfd t (hx₁.trans_le ht.1)).differentiableAt)
    (by
      rw [Set.uIcc_of_le hxb] at hf'c
      exact (hf'c.congr fun t ht ↦ (hfd t (hx₁.trans_le ht.1)).deriv).integrableOn_Icc)
  have hθc : ∀ t : ℝ, ∑ i ∈ Icc 0 ⌊t⌋₊, c i = Chebyshev.theta t := fun t ↦ by
    rw [Chebyshev.theta_eq_sum_Icc, sum_filter]
  simp only [hθc] at habel
  rw [← intervalIntegral.integral_of_le hxb,
    intervalIntegral.integral_congr (g := fun t ↦ f' t * Chebyshev.theta t)
      (fun t ht ↦ by simp only [(hfd t (hmem t ht)).deriv])] at habel
  -- The same identity for `t` in place of `θ`, by the fundamental theorem of calculus.
  have hI₁ : IntervalIntegrable (fun t ↦ f' t * Chebyshev.theta t) volume x b :=
    Chebyshev.theta_mono.intervalIntegrable.continuousOn_mul hf'c
  have hI₂ : IntervalIntegrable (fun t ↦ f' t * t) volume x b :=
    (hf'c.mul continuousOn_id).intervalIntegrable
  have hI₂' : IntervalIntegrable (fun t ↦ -(f' t * t)) volume x b := hI₂.neg
  have hftc : ∫ t in x..b, -(f' t * t) = (L b - b * f b) - (L x - x * f x) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t ↦ L t - t * f t)
      (fun t ht ↦ ?_) hI₂'
    have h := (hasDerivAt_logarithmicIntegralReal_rpow hn (hmem t ht)).fun_sub
      ((hasDerivAt_id' t).fun_mul (hfd t (hmem t ht)))
    convert h using 1
    simp only [hf]
    ring
  rw [intervalIntegral.integral_neg] at hftc
  have hsplit : ∫ t in x..b, f' t * (Chebyshev.theta t - t) =
      (∫ t in x..b, f' t * Chebyshev.theta t) - ∫ t in x..b, f' t * t := by
    rw [← intervalIntegral.integral_sub hI₁ hI₂]
    congr 1
    ext t
    ring
  -- The integral of the error against `f'`.
  have hmaj : ∀ t ∈ Set.uIcc x b, HasDerivAt (fun t ↦ -A / (t ^ (n - 1) * log t ^ (k + 1)))
      (η / (t ^ n * log t ^ (k + 2)) * (n * log t + n * (k + 1) / ((n : ℝ) - 1))) t :=
    fun t ht ↦ hasDerivAt_majorant k hn η (hmem t ht)
  have hmajc : IntervalIntegrable
      (fun t ↦ η / (t ^ n * log t ^ (k + 2)) * (n * log t + n * (k + 1) / ((n : ℝ) - 1)))
      volume x b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht₁ := hmem t ht
    have ht₀ : 0 < t := zero_lt_one.trans ht₁
    have hlog := log_pos ht₁
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))
  have hint : |∫ t in x..b, f' t * (Chebyshev.theta t - t)| ≤
      A / (x ^ (n - 1) * log x ^ (k + 1)) - A / (b ^ (n - 1) * log b ^ (k + 1)) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le hxb
      (f := fun t ↦ f' t * (Chebyshev.theta t - t)) (ae_of_all _ fun t ht ↦ ?_) hmajc
    · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hmaj hmajc] at h
      rw [← Real.norm_eq_abs]
      convert h using 1
      ring
    · have ht₁ : 1 < t := hx₁.trans ht.1
      have ht₀ : 0 < t := zero_lt_one.trans ht₁
      have hlog := log_pos ht₁
      have hk : 1 ≤ n * (k + 1) / ((n : ℝ) - 1) := by
        rw [le_div_iff₀ hn₁]
        have : (0 : ℝ) ≤ k := k.cast_nonneg
        nlinarith
      calc ‖f' t * (Chebyshev.theta t - t)‖
          = (n * log t + 1) / (t ^ (n + 1) * log t ^ 2) * |Chebyshev.theta t - t| := by
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, hf', abs_div, abs_neg,
              abs_of_pos (by positivity), abs_of_pos (by positivity)]
        _ ≤ (n * log t + 1) / (t ^ (n + 1) * log t ^ 2) * (η * t / log t ^ k) := by
            gcongr
            exact (hθ t (hx.trans ht.1.le)).le
        _ = η / (t ^ n * log t ^ (k + 2)) * (n * log t + 1) := by
            field_simp
            ring
        _ ≤ η / (t ^ n * log t ^ (k + 2)) * (n * log t + n * (k + 1) / ((n : ℝ) - 1)) := by
            gcongr
  -- The endpoint term at `b`.
  have hend : |f b * (Chebyshev.theta b - b)| ≤ η / (b ^ (n - 1) * log b ^ (k + 1)) := by
    have hlog := log_pos hb₁
    have hb₀ : 0 < b := zero_lt_one.trans hb₁
    rw [abs_mul, abs_of_pos (by simp only [hf]; positivity), ← weight_mul_eq k (by omega) η hb₁]
    gcongr
    exact (hθ b (hx.trans hxb)).le
  have hηA : η / (b ^ (n - 1) * log b ^ (k + 1)) ≤ A / (b ^ (n - 1) * log b ^ (k + 1)) := by
    have hlog := log_pos hb₁
    have hb₀ : 0 < b := zero_lt_one.trans hb₁
    gcongr
    rw [hA, le_div_iff₀ hn₁]
    nlinarith
  have hx0 : 0 < x := zero_lt_one.trans hx₁
  have hfx : 0 < f x := by
    have hlog := log_pos hx₁
    simp only [hf]
    positivity
  have heq : L x + ∑ i ∈ Ioc ⌊x⌋₊ ⌊b⌋₊, f i * c i - L b =
      f b * (Chebyshev.theta b - b) - f x * (Chebyshev.theta x - x) -
        ∫ t in x..b, f' t * (Chebyshev.theta t - t) := by
    rw [hsplit, habel]
    linarith
  calc |L x + ∑ i ∈ Ioc ⌊x⌋₊ ⌊b⌋₊, f i * c i - L b|
      ≤ |f b * (Chebyshev.theta b - b)| + |f x * (Chebyshev.theta x - x)| +
          |∫ t in x..b, f' t * (Chebyshev.theta t - t)| := by
        rw [heq]
        exact (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ 1 / (x ^ n * log x) * |Chebyshev.theta x - x| + A / (x ^ (n - 1) * log x ^ (k + 1)) := by
        rw [abs_mul (f x), abs_of_pos hfx]
        linarith

end abs_logarithmicIntegral_add_tsum_inv_prime_pow_lt

open abs_logarithmicIntegral_add_tsum_inv_prime_pow_lt in
-- The bound holds for every `k`; the positivity of `k` is not needed.
set_option linter.unusedVariables false in
/-- **Tails of prime power sums from a Chebyshev bound.** Let $k \ge 1$ be an integer and let
$\eta > 0$ and $x_0 > 1$ be reals such that $|\vartheta(y) - y| < \eta y / \log^k y$ for every
real $y \ge x_0$, where $\vartheta(y) = \sum_{p \le y} \log p$ is Chebyshev's function. Then
for every integer $n \ge 2$ and every real $x \ge x_0$,
$$
\Big|\operatorname{li}(x^{1-n}) + \sum_{p > x} \frac{1}{p^n}\Big| <
\frac{\eta}{x^{n-1} \log^{k+1} x} \Big(1 + \frac{n}{n-1}\Big),
$$
where $\operatorname{li}$ is the logarithmic integral and the sums run over primes $p$.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Lemma 6 (`integers-2024-A34-lem-6`). -/
public theorem abs_logarithmicIntegral_add_tsum_inv_prime_pow_lt (k : ℕ) (hk : 0 < k)
    (η x₀ : ℝ) (hη : 0 < η) (hx₀ : 1 < x₀)
    (hθ : ∀ y : ℝ, x₀ ≤ y → |Chebyshev.theta y - y| < η * y / Real.log y ^ k)
    (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : x₀ ≤ x) :
    |Real.logarithmicIntegralReal (x ^ ((1 : ℝ) - n)) +
        ∑' p : ℕ, if p.Prime ∧ x < p then 1 / (p : ℝ) ^ n else 0| <
      η / (x ^ (n - 1) * Real.log x ^ (k + 1)) * (1 + n / (n - 1 : ℝ)) := by
  have hx₁ : 1 < x := hx₀.trans_le hx
  have hx0 : 0 < x := zero_lt_one.trans hx₁
  have hlog := log_pos hx₁
  have hsum : Summable fun p : ℕ ↦ if p.Prime ∧ x < p then 1 / (p : ℝ) ^ n else 0 := by
    refine Summable.of_nonneg_of_le (fun p ↦ ?_) (fun p ↦ ?_)
      (Real.summable_one_div_nat_pow.mpr (by omega : 1 < n))
    · split_ifs <;> positivity
    · split_ifs
      · exact le_rfl
      · positivity
  -- The partial sums up to `N` approach the tail, and `li(N ^ (1 - n))` tends to `0`.
  have hlim := ((tendsto_const_nhds (x := logarithmicIntegralReal (x ^ ((1 : ℝ) - n)))).add
    ((hsum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1))).sub
      (tendsto_logarithmicIntegralReal_rpow hn) |>.abs
  have hle := le_of_tendsto hlim (eventually_atTop.mpr ⟨⌈x⌉₊, fun N hN ↦ by
    have h := abs_partial_sub_le k η x₀ hη hθ hn hx₁ hx (Nat.ceil_le.mp hN)
    rwa [Nat.floor_natCast, ← sum_range_eq_sum_Ioc n hx0.le N] at h⟩)
  rw [sub_zero] at hle
  refine hle.trans_lt ?_
  have h₁ : 1 / (x ^ n * log x) * |Chebyshev.theta x - x| <
      η / (x ^ (n - 1) * log x ^ (k + 1)) := by
    rw [← weight_mul_eq k (by omega) η hx₁]
    exact mul_lt_mul_of_pos_left (hθ x hx) (by positivity)
  have h₂ : η / (x ^ (n - 1) * log x ^ (k + 1)) * (1 + n / (n - 1 : ℝ)) =
      η / (x ^ (n - 1) * log x ^ (k + 1)) +
        η * n / ((n : ℝ) - 1) / (x ^ (n - 1) * log x ^ (k + 1)) := by
    ring
  rw [h₂]
  linarith

end

end MetaMathlibExt
