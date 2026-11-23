/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Axler's bounds for prime counting

The convolution defining the reciprocal coefficients cancels all positive degrees through
the truncation order. The remaining terms in the product have nonpositive coefficients.

The bounds by the auxiliary functions $J$ follow from Abel summation and a two-sided
estimate for Chebyshev's theta function.
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
    | h k ih =>
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

end MetaMathlibExt
