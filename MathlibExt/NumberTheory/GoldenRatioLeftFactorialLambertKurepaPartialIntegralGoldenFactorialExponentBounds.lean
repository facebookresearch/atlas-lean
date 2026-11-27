/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.Analysis.SpecialFunctions.LambertWFunction
public import MathlibExt.NumberTheory.GoldenFactorialExponent
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus


/-!
# Left factorial bounds at the golden factorial exponent

We define Kurepa's partial integral and prove bounds for the left factorial at
its golden factorial exponent.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Theorem 12 (`jis-2024-24.5.7-thm-12`).
-/

namespace MetaMathlibExt

open Real MeasureTheory

@[expose] public section

/-- **Kurepa's partial integral.** For a natural number $n$ and a real number $x$, Kurepa's partial
integral is
$$K_n(x) = \int_0^x e^{-t} \sum_{k=0}^{n-1} t^k \, dt,$$
an oriented integral, so for $x < 0$ it is minus the integral over $[x, 0]$.

The paper writes it as $!n(x) = \int_0^x e^{-t} \frac{t^n - 1}{t - 1} \, dt$; the geometric sum
agrees with $\frac{t^n - 1}{t - 1}$ for $t \ne 1$, and the singularity at $t = 1$ is removable.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 1 (the function `!z(x)`) and Sections 3.1-3.3. -/
public noncomputable def kurepaPartialIntegral (n : ℕ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, Real.exp (-t) * ∑ k ∈ Finset.range n, t ^ k

private def tailPolynomial {R : Type} [Semiring R] : ℕ → R → R
  | 0, _ => 1
  | k + 1, x => x ^ (k + 1) + (k + 1 : ℕ) * tailPolynomial k x

private theorem tailPolynomial_zero (k : ℕ) : tailPolynomial k (0 : ℝ) = k.factorial := by
  induction k with
  | zero => simp [tailPolynomial]
  | succ k ih => simp [tailPolynomial, ih, Nat.factorial_succ]

private theorem tailPolynomial_deriv (k : ℕ) (x : ℝ) :
    HasDerivAt (tailPolynomial k) (tailPolynomial k x - x ^ k) x := by
  induction k with
  | zero => simpa [tailPolynomial] using hasDerivAt_const x (1 : ℝ)
  | succ k ih =>
    convert ((hasDerivAt_id x).pow (k + 1)).add (HasDerivAt.const_mul (k + 1 : ℝ) ih) using 1
    · ext t; simp [tailPolynomial, Nat.cast_add, Nat.cast_one]
    · simp only [tailPolynomial, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_one]
      dsimp
      ring

private theorem tailPolynomial_pos (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 < tailPolynomial k x := by
  induction k with
  | zero => norm_num [tailPolynomial]
  | succ k ih =>
    simp only [tailPolynomial]
    positivity

private theorem integral_monomial (k : ℕ) (x : ℝ) :
    (∫ t in (0 : ℝ)..x, exp (-t) * t ^ k) =
      k.factorial - exp (-x) * tailPolynomial k x := by
  have hd (t : ℝ) : HasDerivAt (fun t => -(exp (-t) * tailPolynomial k t))
      (exp (-t) * t ^ k) t := by
    convert ((((hasDerivAt_id t).neg).exp).mul (tailPolynomial_deriv k t)).neg using 1
    · ext t; rfl
    · dsimp; ring
  have hi : IntervalIntegrable (fun t : ℝ => exp (-t) * t ^ k) volume 0 x := by
    exact ((Real.continuous_exp.comp continuous_neg).mul
      (continuous_id.pow k)).intervalIntegrable _ _
  simpa [tailPolynomial_zero, sub_eq_add_neg, add_comm] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi

private theorem kurepa_formula (n : ℕ) (x : ℝ) :
    kurepaPartialIntegral n x = (∑ k ∈ Finset.range n, (k.factorial : ℝ)) -
      exp (-x) * ∑ k ∈ Finset.range n, tailPolynomial k x := by
  unfold kurepaPartialIntegral
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [integral_monomial]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  · intro k _
    exact ((Real.continuous_exp.comp continuous_neg).mul
      (continuous_id.pow k)).intervalIntegrable _ _

/-- **Kurepa's partial integral stays below the left factorial.** For a natural number $n \ge 1$ and
a real number $x \ge 0$, $K_n(x) < \sum_{k=0}^{n-1} k!$, where the sum is the left factorial $!n$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Sections 3.1-3.3. -/
public theorem kurepaPartialIntegral_lt_sum_factorial (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 0 ≤ x) :
    kurepaPartialIntegral n x < ∑ k ∈ Finset.range n, (k.factorial : ℝ) := by
  rw [kurepa_formula]
  have hp : 0 < ∑ k ∈ Finset.range n, tailPolynomial k x := by
    exact Finset.sum_pos (fun k _ => tailPolynomial_pos k x hx)
      (Finset.nonempty_range_iff.mpr (by omega))
  exact sub_lt_self _ (mul_pos (exp_pos _) hp)

private theorem tailPolynomial_eq_factorial_mul_sum (k : ℕ) (x : ℝ) :
    tailPolynomial k x =
      (k.factorial : ℝ) * ∑ j ∈ Finset.range (k + 1), x ^ j / (j.factorial : ℝ) := by
  induction k with
  | zero => simp [tailPolynomial]
  | succ k ih =>
    have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    rw [tailPolynomial, ih, Finset.sum_range_succ _ (k + 1), Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- **The remainder of Kurepa's partial integral, explicitly.** For a natural number $n$ and a real
number $x$, $\sum_{k=0}^{n-1} k! - K_n(x) = e^{-x} \sum_{k=0}^{n-1} k! \sum_{j=0}^{k} x^j / j!$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Sections 3.1-3.3. -/
public theorem sum_factorial_sub_kurepaPartialIntegral (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range n, (k.factorial : ℝ)) - kurepaPartialIntegral n x =
      exp (-x) * ∑ k ∈ Finset.range n,
        (k.factorial : ℝ) * ∑ j ∈ Finset.range (k + 1), x ^ j / (j.factorial : ℝ) := by
  rw [kurepa_formula, sub_sub_cancel]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => tailPolynomial_eq_factorial_mul_sum k x)

private theorem kurepa_monotone (n : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    kurepaPartialIntegral n x ≤ kurepaPartialIntegral n y := by
  have hi (a b : ℝ) : IntervalIntegrable
      (fun t : ℝ => exp (-t) * ∑ k ∈ Finset.range n, t ^ k) volume a b := by
    apply Continuous.intervalIntegrable
    exact (Real.continuous_exp.comp continuous_neg).mul
      (continuous_finsetSum _ (fun k _ => continuous_id.pow k))
  have hnonneg : 0 ≤ ∫ t in x..y, exp (-t) * ∑ k ∈ Finset.range n, t ^ k := by
    apply intervalIntegral.integral_nonneg hxy
    intro t ht
    exact mul_nonneg (exp_pos _).le
      (Finset.sum_nonneg (fun k _ => pow_nonneg (hx.trans ht.1) k))
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hi 0 x) (hi x y)
  unfold kurepaPartialIntegral
  linarith

private theorem tailPolynomial_bound (n k : ℕ) (hk : k < n) (x : ℝ)
    (hx : 2 * (n : ℝ) ≤ x) : tailPolynomial k x ≤ 2 * x ^ k := by
  have hx0 : 0 ≤ x := (by positivity : (0 : ℝ) ≤ 2 * n).trans hx
  induction k with
  | zero => norm_num [tailPolynomial]
  | succ k ih =>
    have hk' : k < n := by omega
    have hkn : (k + 1 : ℝ) ≤ n := by exact_mod_cast (show k + 1 ≤ n by omega)
    have hb := mul_le_mul_of_nonneg_left (ih hk') (by positivity : (0 : ℝ) ≤ k + 1)
    simp only [tailPolynomial, Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith [pow_nonneg hx0 k]

private theorem sum_pow_bound (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 2 ≤ x) :
    ∑ k ∈ Finset.range n, x ^ k ≤ 2 * x ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  induction m with
  | zero => norm_num
  | succ m ih =>
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at ih ⊢
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [ih (by omega), pow_nonneg (by linarith : 0 ≤ x) m]

private theorem totalTail_bound (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : 2 * (n : ℝ) ≤ x) :
    ∑ k ∈ Finset.range n, tailPolynomial k x ≤ 4 * x ^ (n - 1) := by
  have hb := Finset.sum_le_sum (fun k hk =>
    tailPolynomial_bound n k (Finset.mem_range.mp hk) x hx)
  rw [← Finset.mul_sum] at hb
  have hx2 : 2 ≤ x := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  linarith [sum_pow_bound n hn x hx2]

private theorem goldenRatio_bound : goldenRatio < 16181 / 10000 := by
  nlinarith [goldenRatio_sq, goldenRatio_pos]

private theorem log_lower (n : ℕ) (hn : 40 ≤ n) : 11 / 3 ≤ log (n : ℝ) := by
  have hn40 : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have he4 : exp (4 : ℝ) < (68 / 25 : ℝ) ^ 4 := by
    rw [show exp (4 : ℝ) = exp 1 ^ 4 by rw [← exp_nat_mul]; norm_num]
    exact pow_lt_pow_left₀ (exp_one_lt_d9.trans (by norm_num)) (exp_pos _).le (by decide)
  have hb := sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 / 3 by norm_num) 3
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  have he : exp (11 / 3 : ℝ) < 40 := calc
    _ = exp 4 / exp (1 / 3) := by rw [← exp_sub]; norm_num
    _ < _ := by
      rw [div_lt_iff₀ (exp_pos _)]
      norm_num at he4
      linarith
  exact (le_log_iff_exp_le hn0).mpr (he.le.trans hn40)

private theorem log_factorial_bound (n : ℕ) (hn : 40 ≤ n) :
    3 / 2 * (n : ℝ) * log n ≤ goldenFactorialExponent n := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hlog := log_lower n hn
  have hseries := sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 121 / 125 by norm_num) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hseries
  have hphi : goldenRatio ^ 2 < exp (121 / 125 : ℝ) := by
    rw [goldenRatio_sq]
    linarith [goldenRatio_bound]
  have hlogphi : 2 * log goldenRatio < 121 / 125 := by
    have h := log_lt_log (pow_pos goldenRatio_pos 2) hphi
    rw [log_pow, log_exp] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hst := Stirling.le_log_factorial_stirling (n := n) (by omega)
  have hpilog : 0 ≤ log (2 * Real.pi) := log_nonneg (by linarith [Real.two_le_pi])
  have hfactlog := log_le_log (by positivity : (0 : ℝ) < n.factorial)
    (goldenFactorialExponent_mem n).2
  rw [log_pow] at hfactlog
  have ha0 : (0 : ℝ) ≤ goldenFactorialExponent n := by positivity
  have hprod := mul_le_mul_of_nonneg_left hlogphi.le ha0
  nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hlog)]

private theorem large_cutoff_bound (n : ℕ) (hn : 40 ≤ n) :
    ∃ x : ℝ, 2 * (n : ℝ) ≤ x ∧ x ≤ goldenFactorialExponent n ∧
      4 * x ^ (n - 1) < exp x := by
  have hn40 : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hlog : 0 < log n := log_pos (by linarith)
  let x : ℝ := 3 / 2 * (n : ℝ) * log n
  have hx0 : 0 < x := by positivity
  have hlogn := log_lower n hn
  have hx2 : 2 * (n : ℝ) ≤ x := by
    dsimp [x]
    nlinarith
  have hsqrt : 6 ≤ sqrt (n : ℝ) := by
    rw [le_sqrt (by norm_num) hn0.le]
    norm_num
    omega
  have hsqrt0 : 0 < sqrt (n : ℝ) := sqrt_pos.mpr hn0
  have hlog2 : log (2 : ℝ) ≤ 3 / 4 := log_two_lt_d9.le.trans (by norm_num)
  have hlogsqrt : log (sqrt (n : ℝ)) ≤ 1 / 2 + sqrt (n : ℝ) / 4 := by
    have hb := log_le_sub_one_of_pos (show 0 < sqrt (n : ℝ) / 4 by positivity)
    rw [log_div hsqrt0.ne' (by norm_num)] at hb
    have hl4 : log (4 : ℝ) ≤ 3 / 2 := by
      have h : log (4 : ℝ) = 2 * log 2 := by
        have h := log_pow (2 : ℝ) 2
        norm_num only [Nat.cast_ofNat, pow_two] at h
        exact h
      linarith
    linarith
  have hbase : 3 / 2 * log (n : ℝ) ≤ sqrt (n : ℝ) := by
    rw [log_sqrt hn0.le] at hlogsqrt
    linarith
  have hlogx : log x ≤ 3 / 2 * log (n : ℝ) := by
    have hb := log_le_log (show 0 < 3 / 2 * log (n : ℝ) by positivity) hbase
    rw [log_sqrt hn0.le] at hb
    have heq : log x = log (n : ℝ) + log (3 / 2 * log (n : ℝ)) := by
      rw [show x = (n : ℝ) * (3 / 2 * log (n : ℝ)) by dsimp [x]; ring,
        log_mul hn0.ne' (by positivity)]
    linarith
  have hpow : x ^ n ≤ exp x := by
    rw [← exp_log (pow_pos hx0 n), log_pow]
    apply exp_le_exp.mpr
    dsimp [x] at hlogx ⊢
    nlinarith
  refine ⟨x, hx2, log_factorial_bound n hn, lt_of_lt_of_le ?_ hpow⟩
  have heq : x ^ n = x ^ (n - 1) * x := by
    rw [← pow_succ, show n - 1 + 1 = n by omega]
  rw [heq]
  have : 4 < x := by linarith
  simpa [mul_comm] using mul_lt_mul_of_pos_right this (pow_pos hx0 (n - 1))

private theorem tailPolynomial_natCast (k m : ℕ) :
    ((tailPolynomial k m : ℕ) : ℝ) = tailPolynomial k (m : ℝ) := by
  induction k with
  | zero => simp [tailPolynomial]
  | succ k ih => simp [tailPolynomial, ih]

private def smallCutoff (n : ℕ) : ℕ :=
  ([0, 1, 2, 4, 7, 10, 14, 18, 23, 27, 32, 37, 42, 47, 53, 58, 64, 70, 76, 82, 88,
    95, 101, 108, 114, 121, 128, 135, 142, 149, 156, 163, 170, 177, 185, 192, 199, 207,
    214, 222] : List ℕ).getD n 0

private theorem small_certificate : ∀ n ∈ Finset.Ico 2 40,
    1 ≤ smallCutoff n ∧
      16181 ^ (smallCutoff n - 1) < n.factorial * 10000 ^ (smallCutoff n - 1) ∧
      (∑ k ∈ Finset.range n, tailPolynomial k (smallCutoff n)) * 500 ^ smallCutoff n <
        1359 ^ smallCutoff n := by
  decide

private theorem small_cutoff_bound (n : ℕ) (hn : 2 ≤ n) (hn40 : n < 40) :
    ∃ x : ℝ, 0 ≤ x ∧ x ≤ goldenFactorialExponent n ∧
      (∑ k ∈ Finset.range n, tailPolynomial k x) < exp x := by
  obtain ⟨hm, hphi, hpoly⟩ := small_certificate n (Finset.mem_Ico.mpr ⟨hn, hn40⟩)
  let m := smallCutoff n
  have hphi' : (16181 : ℝ) ^ (m - 1) < (n.factorial : ℝ) * 10000 ^ (m - 1) := by
    exact_mod_cast hphi
  have hphi_bound := goldenRatio_bound
  have hfact : goldenRatio ^ (m - 1) < (n.factorial : ℝ) := calc
    _ ≤ (16181 / 10000 : ℝ) ^ (m - 1) :=
      pow_le_pow_left₀ goldenRatio_pos.le hphi_bound.le _
    _ < _ := by
      rw [div_pow, div_lt_iff₀ (by positivity)]
      exact hphi'
  have hma : m ≤ goldenFactorialExponent n := by
    have hga := (goldenFactorialExponent_mem n).2
    have hlt : goldenRatio ^ (m - 1) < goldenRatio ^ goldenFactorialExponent n :=
      hfact.trans_le hga
    have hexp := (pow_lt_pow_iff_right₀ one_lt_goldenRatio).mp hlt
    omega
  have hpoly' : (∑ k ∈ Finset.range n, tailPolynomial k (m : ℝ)) * 500 ^ m <
      (1359 : ℝ) ^ m := by
    have h : ((∑ k ∈ Finset.range n, tailPolynomial k m : ℕ) : ℝ) * 500 ^ m <
        (1359 : ℝ) ^ m := by exact_mod_cast hpoly
    simpa only [Nat.cast_sum, tailPolynomial_natCast] using h
  have htail : (∑ k ∈ Finset.range n, tailPolynomial k (m : ℝ)) <
      (1359 / 500 : ℝ) ^ m := by
    rw [div_pow, lt_div_iff₀ (by positivity)]
    exact hpoly'
  have he : (1359 / 500 : ℝ) ^ m < exp (m : ℝ) := by
    rw [show (m : ℝ) = (m : ℝ) * 1 by ring, exp_nat_mul]
    exact pow_lt_pow_left₀ (exp_one_gt_d9.trans_le' (by norm_num)) (by norm_num) (by omega)
  exact ⟨m, by positivity, by exact_mod_cast hma, htail.trans he⟩

/-- **Left factorial bounds at the golden factorial exponent.** For every integer $n \ge 1$, let
$!n = \sum_{k=0}^{n-1} k!$ be the left factorial, let
$K_n(x) = \int_0^x e^{-t} \sum_{k=0}^{n-1} t^k \, dt$ be Kurepa's partial integral, and let
$\alpha(n)$ be the least positive integer $m$ with $n! \le \varphi^m$, where $\varphi$ is the
golden ratio. Then $\beta(n) = K_n(\alpha(n))$ satisfies $\beta(n) < {!n} < \beta(n) + 1$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Theorem 12 (`jis-2024-24.5.7-thm-12`). -/
public theorem kurepaPartialIntegral_goldenFactorialExponent_bounds (n : ℕ)
    (hn : 1 ≤ n) :
    kurepaPartialIntegral n (goldenFactorialExponent n) <
        ∑ k ∈ Finset.range n, (k.factorial : ℝ) ∧
      ∑ k ∈ Finset.range n, (k.factorial : ℝ) <
        kurepaPartialIntegral n (goldenFactorialExponent n) + 1 := by
  have ha : (0 : ℝ) ≤ goldenFactorialExponent n := by positivity
  refine ⟨kurepaPartialIntegral_lt_sum_factorial n hn _ ha, ?_⟩
  have hx : ∃ x : ℝ, 0 ≤ x ∧ x ≤ goldenFactorialExponent n ∧
      (∑ k ∈ Finset.range n, tailPolynomial k x) < exp x := by
    by_cases hlarge : 40 ≤ n
    · obtain ⟨x, hx, hxa, hbound⟩ := large_cutoff_bound n hlarge
      have hx0 : 0 ≤ x := (by positivity : (0 : ℝ) ≤ 2 * n).trans hx
      exact ⟨x, hx0, hxa, (totalTail_bound n hn x hx).trans_lt hbound⟩
    · by_cases hone : n = 1
      · subst n
        refine ⟨1, by norm_num, by simp [goldenFactorialExponent_one], ?_⟩
        simp [tailPolynomial]
      · exact small_cutoff_bound n (by omega) (by omega)
  obtain ⟨x, hx0, hxa, htail⟩ := hx
  have herror : exp (-x) * (∑ k ∈ Finset.range n, tailPolynomial k x) < 1 := by
    rw [exp_neg, ← div_eq_inv_mul, div_lt_one (exp_pos _)]
    exact htail
  have hb : (∑ k ∈ Finset.range n, (k.factorial : ℝ)) < kurepaPartialIntegral n x + 1 := by
    rw [kurepa_formula]
    linarith
  have hmono := kurepa_monotone n hx0 hxa
  linarith

end

end MetaMathlibExt
