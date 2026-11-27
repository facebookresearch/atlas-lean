/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Numerical constants of Gaudron and Rémond's isogeny estimate

Three numerical steps of É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J.
163 (2014), 2057–2108:

* `GaudronRemond.eightPeriods_constant_le_exp`: the constant of the end of the proof of Lemme 8.4,
  p. 2094, for `ε = 1/8`, is at most `e^12.5`;
* `GaudronRemond.c₂_le`, `GaudronRemond.key_le_two_pow` and `GaudronRemond.c₁_mul_c₂_le`: the
  bounds `c₂(b) ≤ 287 b³`, `1600 × 287 × e^12.5 (4b)^12 b^9 ≤ 2^(64 b²)` and
  `c₁(b) c₂(b) ≤ (8b)^(64 b²)` of p. 2097, for the constants `c₁(b)` and `c₂(b)` of p. 2096;
* `GaudronRemond.isogeny_bound_exponents`: the exponent computation of the proof of Lemme 9.3,
  pp. 2099–2100, giving the bound `(9g)^(96 g⁴) P^(2^10 g³)`.
-/

@[expose] public section

open Real

namespace GaudronRemond

/-! ### The norms of the eight periods -/

/-- `12 log π ≤ 53 log 2 - 23`, from `π^12 e^23 ≤ 2^53`. -/
private lemma twelve_mul_log_pi_le : 12 * log π ≤ 53 * log 2 - 23 := by
  have hpi : π ^ 12 ≤ (3.141593 : ℝ) ^ 12 := pow_le_pow_left₀ pi_pos.le pi_lt_d6.le 12
  have he : exp 23 ≤ (2.7182818286 : ℝ) ^ 23 := by
    rw [← show ((23 : ℕ) : ℝ) = 23 by norm_num, ← exp_one_pow]
    exact pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 23
  have hprod : π ^ 12 * exp 23 ≤ 2 ^ 53 := by
    calc π ^ 12 * exp 23 ≤ (3.141593 : ℝ) ^ 12 * (2.7182818286 : ℝ) ^ 23 := by
          gcongr
      _ ≤ 2 ^ 53 := by norm_num
  have := log_le_log (by positivity) hprod
  rw [log_mul (by positivity) (exp_pos 23).ne', log_pow, log_exp, log_pow] at this
  push_cast at this
  linarith

/-- `e^12.5 > 2.7182818283^12 × 1.6487212`. -/
private lemma exp_twelve_point_five_gt : (2.7182818283 : ℝ) ^ 12 * 1.6487212 < exp 12.5 := by
  have hhalf : (1.6487212 : ℝ) < exp (1 / 2) := by
    have hsq : exp (1 / 2) ^ 2 = exp 1 := by
      rw [← exp_nat_mul]; norm_num
    have h1 : (1.6487212 : ℝ) ^ 2 < exp (1 / 2) ^ 2 := by
      rw [hsq]; linarith [exp_one_gt_d9]
    exact lt_of_pow_lt_pow_left₀ 2 (exp_pos _).le h1
  have h12 : (2.7182818283 : ℝ) ^ 12 < exp 1 ^ 12 :=
    pow_lt_pow_left₀ exp_one_gt_d9 (by norm_num) (by norm_num)
  have hsplit : exp 12.5 = exp 1 ^ 12 * exp (1 / 2) := by
    rw [exp_one_pow, ← exp_add]; norm_num
  rw [hsplit]
  calc (2.7182818283 : ℝ) ^ 12 * 1.6487212 < exp 1 ^ 12 * 1.6487212 := by gcongr
    _ < exp 1 ^ 12 * exp (1 / 2) := by gcongr

/-- **The constant for the norms of the eight periods.** For $\varepsilon = 1/8$,
$$\frac{6 \times 16^2}{(1 - \varepsilon)\pi} \Bigl(136 + 68 \log \frac{2\pi^2}{\varepsilon}\Bigr)
\le e^{12.5}.$$
The left side is about $268\,332.3$ and $e^{12.5}$ about $268\,337.3$. The proof uses
$3.141592 < \pi < 3.141593$, $\log 2 < 0.6931471808$, $e > 2.7182818283$, $e < 2.7182818286$ and
$12 \log \pi \le 53 \log 2 - 23$.

This is the choice of $\varepsilon$ that ends Gaudron and Rémond's proof of Lemme 8.4: the left
side is the constant left after factoring $b^4 \max(1, h_F(A), h_F(B))$ out of the bound given by
Autissier's matrix lemma.

Source: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, <https://doi.org/10.1215/00127094-2782528>, the end of the proof of Lemme 8.4,
p. 2094. -/
theorem eightPeriods_constant_le_exp :
    6 * 16 ^ 2 / ((1 - 1 / 8) * π) * (136 + 68 * log (2 * π ^ 2 / (1 / 8))) ≤ exp 12.5 := by
  have hlog : log (2 * π ^ 2 / (1 / 8)) = 4 * log 2 + 2 * log π := by
    rw [show 2 * π ^ 2 / (1 / 8) = 2 ^ 4 * π ^ 2 by ring,
      log_mul (by positivity) (by positivity), log_pow, log_pow]
    push_cast; ring
  rw [hlog]
  have hl := log_two_lt_d9
  have hlp := twelve_mul_log_pi_le
  have hB : 136 + 68 * (4 * log 2 + 2 * log π) ≤
      136 + 68 * (4 * 0.6931471808 + (53 * 0.6931471808 - 23) / 6) := by
    linarith
  have hB0 : 0 ≤ 136 + 68 * (4 * log 2 + 2 * log π) := by
    have : 0 ≤ log 2 := log_nonneg (by norm_num)
    have : 0 ≤ log π := log_nonneg (by linarith [pi_gt_three])
    linarith
  have hA : 6 * 16 ^ 2 / ((1 - 1 / 8) * π) ≤ 6 * 16 ^ 2 / ((1 - 1 / 8) * 3.141592) := by
    gcongr
    exact pi_gt_d6.le
  calc 6 * 16 ^ 2 / ((1 - 1 / 8) * π) * (136 + 68 * (4 * log 2 + 2 * log π))
      ≤ 6 * 16 ^ 2 / ((1 - 1 / 8) * 3.141592) *
          (136 + 68 * (4 * 0.6931471808 + (53 * 0.6931471808 - 23) / 6)) := by
        gcongr
    _ ≤ (2.7182818283 : ℝ) ^ 12 * 1.6487212 := by norm_num
    _ ≤ exp 12.5 := exp_twelve_point_five_gt.le

/-! ### The constant of the period theorem construction -/

/-- Gaudron and Rémond's constant $c_1(b) = 1600\, e^{12.5} (4b)^{64 b^2 + 12} b^6$.

Source: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, <https://doi.org/10.1215/00127094-2782528>, p. 2096. -/
noncomputable def c₁ (b : ℕ) : ℝ :=
  1600 * exp 12.5 * (4 * b : ℝ) ^ (64 * b ^ 2 + 12) * (b : ℝ) ^ 6

/-- Gaudron and Rémond's constant
$c_2(b) = 174 + \log 800 + (64 b^2 + 12) \log(4b) + 6 \log b$.

Source: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, <https://doi.org/10.1215/00127094-2782528>, p. 2096. -/
noncomputable def c₂ (b : ℕ) : ℝ :=
  174 + log 800 + (64 * (b : ℝ) ^ 2 + 12) * log (4 * b) + 6 * log b

/-- **Bound for $c_2(b)$.** For every integer $b \ge 1$, $c_2(b) \le 287\, b^3$. At $b = 1$,
$c_2(1) \approx 286.04$.

The proof bounds $\log 800 \le 10 \log 2$, $\log(4b) \le 2 \log 2 + b - 1$ and
$\log b \le b - 1$, with $\log 2 < 0.6931471808$.

Source: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, <https://doi.org/10.1215/00127094-2782528>, p. 2097 ("On majore $c_2(b)$ par
$287 b^3$"). -/
theorem c₂_le (b : ℕ) (hb : 1 ≤ b) : c₂ b ≤ 287 * (b : ℝ) ^ 3 := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hl := log_two_lt_d9
  have h800 : log 800 ≤ 10 * log 2 := by
    have := log_le_log (by norm_num : (0 : ℝ) < 800) (by norm_num : (800 : ℝ) ≤ 2 ^ 10)
    rwa [log_pow] at this
  have hlogb : log b ≤ (b : ℝ) - 1 := log_le_sub_one_of_pos (by linarith)
  have hlog4b : log (4 * b) ≤ 2 * log 2 + ((b : ℝ) - 1) := by
    rw [log_mul (by norm_num) (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    push_cast; linarith
  have hcoef : 0 ≤ 64 * (b : ℝ) ^ 2 + 12 := by positivity
  have h1 : (64 * (b : ℝ) ^ 2 + 12) * log (4 * b) ≤
      (64 * (b : ℝ) ^ 2 + 12) * ((b : ℝ) + 0.3862943616) := by
    apply mul_le_mul_of_nonneg_left _ hcoef
    linarith
  rw [c₂]
  nlinarith [mul_nonneg (sub_nonneg.mpr hbR) (sub_nonneg.mpr hbR),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hbR) (sub_nonneg.mpr hbR)) (sub_nonneg.mpr hbR)]

/-- **The key numerical inequality.** For every integer $b \ge 1$,
$$1600 \times 287 \times e^{12.5} (4b)^{12} b^9 \le 2^{64 b^2}.$$

The proof uses $e^{12.5} \le e^{13} < 2.7182818286^{13}$ and $b \le 2^{b-1}$, which reduce the
inequality to $b = 1$.

Source: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, <https://doi.org/10.1215/00127094-2782528>, p. 2097. -/
theorem key_le_two_pow (b : ℕ) (hb : 1 ≤ b) :
    1600 * 287 * exp 12.5 * (4 * b : ℝ) ^ 12 * (b : ℝ) ^ 9 ≤ 2 ^ (64 * b ^ 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
  have hbk : ((k + 1 : ℕ) : ℝ) ≤ 2 ^ k := by
    have : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    exact_mod_cast this
  have he : exp 12.5 ≤ (2.7182818286 : ℝ) ^ 13 := by
    calc exp 12.5 ≤ exp 13 := exp_le_exp.mpr (by norm_num)
      _ = exp 1 ^ 13 := by rw [exp_one_pow]; norm_num
      _ ≤ (2.7182818286 : ℝ) ^ 13 := pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 13
  have hb0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
  have hpow : (4 * ((k + 1 : ℕ) : ℝ)) ^ 12 * ((k + 1 : ℕ) : ℝ) ^ 9 ≤
      4 ^ 12 * (2 : ℝ) ^ (21 * k) := by
    rw [mul_pow, mul_assoc, ← pow_add, pow_mul']
    gcongr
  have hexp : (2 : ℝ) ^ (21 * k) ≤ 2 ^ (64 * (k + 1) ^ 2 - 64) := by
    refine pow_le_pow_right₀ (by norm_num) ?_
    have h : 64 * (k + 1) ^ 2 = 64 * k ^ 2 + 128 * k + 64 := by ring
    omega
  have hsplit : (2 : ℝ) ^ (64 * (k + 1) ^ 2) = 2 ^ 64 * 2 ^ (64 * (k + 1) ^ 2 - 64) := by
    rw [← pow_add]; congr 1
    have : 64 ≤ 64 * (k + 1) ^ 2 := by nlinarith
    omega
  rw [hsplit]
  calc 1600 * 287 * exp 12.5 * (4 * ((k + 1 : ℕ) : ℝ)) ^ 12 * ((k + 1 : ℕ) : ℝ) ^ 9
      = 1600 * 287 * exp 12.5 * ((4 * ((k + 1 : ℕ) : ℝ)) ^ 12 * ((k + 1 : ℕ) : ℝ) ^ 9) := by
        ring
    _ ≤ 1600 * 287 * (2.7182818286 : ℝ) ^ 13 * (4 ^ 12 * (2 : ℝ) ^ (21 * k)) := by gcongr
    _ ≤ 1600 * 287 * (2.7182818286 : ℝ) ^ 13 * (4 ^ 12 * 2 ^ (64 * (k + 1) ^ 2 - 64)) := by
        gcongr
    _ = (1600 * 287 * (2.7182818286 : ℝ) ^ 13 * 4 ^ 12) * 2 ^ (64 * (k + 1) ^ 2 - 64) := by
        ring
    _ ≤ 2 ^ 64 * 2 ^ (64 * (k + 1) ^ 2 - 64) := by
        gcongr
        norm_num

/-- **Numerical bound for the constant of the period theorem construction.** For every integer
$b \ge 1$, with $c_1(b) = 1600\, e^{12.5} (4b)^{64 b^2 + 12} b^6$ and
$c_2(b) = 174 + \log 800 + (64 b^2 + 12) \log(4b) + 6 \log b$,
$$c_1(b)\, c_2(b) \le (8b)^{64 b^2}.$$
It is the product of `GaudronRemond.c₂_le` and `GaudronRemond.key_le_two_pow` with
$(4b)^{64 b^2}$.

Source: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, <https://doi.org/10.1215/00127094-2782528>, the definitions of $c_1(b)$ and $c_2(b)$,
p. 2096, and the estimate $c(b) \le (8b)^{64 b^2}$ for $c(b) = c_1(b) c_2(b)$, p. 2097. -/
theorem c₁_mul_c₂_le (b : ℕ) (hb : 1 ≤ b) : c₁ b * c₂ b ≤ (8 * b : ℝ) ^ (64 * b ^ 2) := by
  have hc₁ : 0 ≤ c₁ b := by rw [c₁]; positivity
  calc c₁ b * c₂ b ≤ c₁ b * (287 * (b : ℝ) ^ 3) := mul_le_mul_of_nonneg_left (c₂_le b hb) hc₁
    _ = (4 * b : ℝ) ^ (64 * b ^ 2) *
          (1600 * 287 * exp 12.5 * (4 * b : ℝ) ^ 12 * (b : ℝ) ^ 9) := by
        rw [c₁]; ring
    _ ≤ (4 * b : ℝ) ^ (64 * b ^ 2) * 2 ^ (64 * b ^ 2) := by
        gcongr
        exact key_le_two_pow b hb
    _ = (8 * b : ℝ) ^ (64 * b ^ 2) := by
        rw [← mul_pow]; ring_nf

/-! ### The exponents of the isogeny bound -/

/-- For natural numbers `f i`, `∑ (f i)³ ≤ (∑ f i)³`. -/
private lemma sum_cube_le_cube_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    ∑ i ∈ s, f i ^ 3 ≤ (∑ i ∈ s, f i) ^ 3 := by
  calc ∑ i ∈ s, f i ^ 3 = ∑ i ∈ s, f i * f i ^ 2 := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_; ring
    _ ≤ ∑ i ∈ s, f i * (∑ j ∈ s, f j) ^ 2 := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        gcongr
        exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le _) hi
    _ = (∑ i ∈ s, f i) ^ 3 := by rw [← Finset.sum_mul]; ring

/-- **The exponent computation of the isogeny bound.** Let $g \ge 1$ be an integer,
$n_1, \dots, n_t, g_1, \dots, g_t, d_1, \dots, d_t$ natural numbers with
$\sum_{i=1}^t n_i g_i = g$, and $\nu, \nu_1, \dots, \nu_t$ real numbers with
$$\nu \le 2 g^2, \qquad d_i \le 2 g_i^2, \qquad d_i \nu_i \le 2 g_i^2 \quad (1 \le i \le t).$$
Let $P \ge 1$ and $L, L_1, \dots, L_t > 0$ be real numbers with
$$L \le 2^{-116} (9g)^{8g} P^{64 \nu}, \qquad L_i \le (9g)^{4g} P^{32 \nu_i} \quad
(1 \le i \le t).$$
Then
$$(10 g)^{5g}\, L^{4g} \prod_{i=1}^t L_i^{8 n_i^2 g_i d_i} \le (9g)^{96 g^4} P^{2^{10} g^3}.$$
In Gaudron and Rémond's setting $t \ge 1$, the $n_i, g_i, d_i$ are at least $1$ and
$\nu, \nu_i \ge 0$; the inequality does not need these hypotheses.

This is the computation of the proof of Lemme 9.3, with $L = \Lambda \Lambda'$, $L_i = \Lambda_i$,
$\nu = \nu(A)$ and $\nu_i = \nu(A_i)$, the bounds for $L$ and $L_i$ being those of Lemme 9.2.

Source: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, <https://doi.org/10.1215/00127094-2782528>, the proof of Lemme 9.3, pp. 2099–2100
(the bound $g^{5g} (9g)^{32 g^2 + 32 g \sum_i n_i^2 g_i d_i}
P^{256 (g \nu(A) + \sum_i n_i^2 g_i d_i \nu(A_i))}$, the bounds $d_i \le d_i \nu(A_i) \le 2 g_i^2$
and $\nu(A) \le 2 g^2$, and $g^{5g} \le (9g)^{32 g^2 (g^2 - 1)}$). -/
theorem isogeny_bound_exponents {t : ℕ} (g : ℕ) (hg : 1 ≤ g) (n gi d : Fin t → ℕ)
    (hsum : ∑ i, n i * gi i = g) (ν : ℝ) (νi : Fin t → ℝ) (hν : ν ≤ 2 * (g : ℝ) ^ 2)
    (hd : ∀ i, d i ≤ 2 * gi i ^ 2) (hdν : ∀ i, (d i : ℝ) * νi i ≤ 2 * (gi i : ℝ) ^ 2)
    (P L : ℝ) (Li : Fin t → ℝ) (hP : 1 ≤ P) (hL : 0 < L) (hLi : ∀ i, 0 < Li i)
    (hLb : L ≤ 2 ^ (-116 : ℤ) * (9 * g : ℝ) ^ (8 * g) * P ^ (64 * ν))
    (hLib : ∀ i, Li i ≤ (9 * g : ℝ) ^ (4 * g) * P ^ (32 * νi i)) :
    (10 * g : ℝ) ^ (5 * g) * L ^ (4 * g) * ∏ i, Li i ^ (8 * n i ^ 2 * gi i * d i) ≤
      (9 * g : ℝ) ^ (96 * g ^ 4) * P ^ (2 ^ 10 * g ^ 3) := by
  set X : ℝ := 9 * g with hX
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hX1 : 1 ≤ X := by rw [hX]; linarith
  have hP0 : 0 < P := by linarith
  set e : Fin t → ℕ := fun i ↦ 8 * n i ^ 2 * gi i * d i with he
  -- The sums `S = ∑ n_i² g_i d_i ≤ 2 g³` and `T = ∑ n_i² g_i d_i ν_i ≤ 2 g³`.
  have hcube : ∑ i, n i ^ 2 * gi i ^ 3 ≤ g ^ 3 := by
    rw [← hsum]
    refine le_trans (Finset.sum_le_sum fun i _ ↦ ?_) (sum_cube_le_cube_sum _ _)
    rw [mul_pow]
    have hn : n i ^ 2 ≤ n i ^ 3 := by
      rcases Nat.eq_zero_or_pos (n i) with h | h
      · simp [h]
      · exact Nat.pow_le_pow_right h (by norm_num)
    exact Nat.mul_le_mul_right _ hn
  have hS : ∑ i, e i ≤ 16 * g ^ 3 := by
    calc ∑ i, e i ≤ ∑ i, 16 * (n i ^ 2 * gi i ^ 3) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          simp only [he]
          have := hd i
          calc 8 * n i ^ 2 * gi i * d i ≤ 8 * n i ^ 2 * gi i * (2 * gi i ^ 2) := by gcongr
            _ = 16 * (n i ^ 2 * gi i ^ 3) := by ring
      _ = 16 * ∑ i, n i ^ 2 * gi i ^ 3 := by rw [Finset.mul_sum]
      _ ≤ 16 * g ^ 3 := by gcongr
  have hcubeR : ∑ i, (n i : ℝ) ^ 2 * (gi i : ℝ) ^ 3 ≤ (g : ℝ) ^ 3 := by
    exact_mod_cast hcube
  have hT : ∑ i, 32 * νi i * (e i : ℝ) ≤ 512 * (g : ℝ) ^ 3 := by
    calc ∑ i, 32 * νi i * (e i : ℝ) ≤ ∑ i, 512 * ((n i : ℝ) ^ 2 * (gi i : ℝ) ^ 3) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          simp only [he]
          push_cast
          have h := mul_le_mul_of_nonneg_left (hdν i)
            (by positivity : (0 : ℝ) ≤ 256 * (n i : ℝ) ^ 2 * (gi i : ℝ))
          nlinarith
      _ = 512 * ∑ i, (n i : ℝ) ^ 2 * (gi i : ℝ) ^ 3 := by rw [Finset.mul_sum]
      _ ≤ 512 * (g : ℝ) ^ 3 := by gcongr
  -- Inserting the bounds for `L` and the `L_i`.
  have hL4 : L ^ (4 * g) ≤ ((2 : ℝ) ^ (-116 : ℤ)) ^ (4 * g) * X ^ (32 * g ^ 2) *
      P ^ (256 * g * ν) := by
    calc L ^ (4 * g) ≤ (2 ^ (-116 : ℤ) * X ^ (8 * g) * P ^ (64 * ν)) ^ (4 * g) :=
          pow_le_pow_left₀ hL.le hLb _
      _ = ((2 : ℝ) ^ (-116 : ℤ)) ^ (4 * g) * X ^ (32 * g ^ 2) * P ^ (256 * g * ν) := by
          rw [mul_pow, mul_pow, ← pow_mul, ← rpow_mul_natCast hP0.le]
          congr 2
          · ring
          · push_cast; ring
  have hLiprod : ∏ i, Li i ^ e i ≤ X ^ (4 * g * ∑ i, e i) * P ^ (∑ i, 32 * νi i * (e i : ℝ)) := by
    calc ∏ i, Li i ^ e i ≤ ∏ i, (X ^ (4 * g) * P ^ (32 * νi i)) ^ e i := by
          refine Finset.prod_le_prod₀ (fun i _ ↦ ?_) (fun i _ ↦ ?_)
          · exact pow_nonneg (hLi i).le _
          · exact pow_le_pow_left₀ (hLi i).le (hLib i) _
      _ = ∏ i, (X ^ (4 * g * e i) * P ^ (32 * νi i * (e i : ℝ))) := by
          refine Finset.prod_congr rfl fun i _ ↦ ?_
          rw [mul_pow, ← pow_mul, ← rpow_mul_natCast hP0.le]
      _ = X ^ (4 * g * ∑ i, e i) * P ^ (∑ i, 32 * νi i * (e i : ℝ)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.mul_sum,
            rpow_sum_of_pos hP0]
  -- `(10 g)^(5g) 2^(-464 g) ≤ g^(5g)`.
  have h10 : (10 * g : ℝ) ^ (5 * g) * ((2 : ℝ) ^ (-116 : ℤ)) ^ (4 * g) ≤ (g : ℝ) ^ (5 * g) := by
    have hsplit : (10 * g : ℝ) ^ (5 * g) * ((2 : ℝ) ^ (-116 : ℤ)) ^ (4 * g) =
        (10 ^ 5 * ((2 : ℝ) ^ (-116 : ℤ)) ^ 4) ^ g * (g : ℝ) ^ (5 * g) := by
      rw [mul_pow, pow_mul, pow_mul, pow_mul, mul_pow]; ring
    rw [hsplit]
    refine mul_le_of_le_one_left (by positivity) (pow_le_one₀ (by positivity) ?_)
    norm_num
  -- `g^(5g) ≤ (9g)^(32 g² (g² - 1))`.
  have hg5 : (g : ℝ) ^ (5 * g) ≤ X ^ (32 * g ^ 2 * (g ^ 2 - 1)) := by
    rcases Nat.lt_or_ge g 2 with h | h
    · obtain rfl : g = 1 := by omega
      norm_num
    · calc (g : ℝ) ^ (5 * g) ≤ X ^ (5 * g) := pow_le_pow_left₀ (by positivity) (by linarith) _
        _ ≤ X ^ (32 * g ^ 2 * (g ^ 2 - 1)) := by
            refine pow_le_pow_right₀ hX1 ?_
            have h3 : 3 ≤ g ^ 2 - 1 := by
              have : 4 ≤ g ^ 2 := by nlinarith
              omega
            nlinarith
  -- Combining.
  have hXexp : 32 * g ^ 2 * (g ^ 2 - 1) + (32 * g ^ 2 + 4 * g * ∑ i, e i) ≤ 96 * g ^ 4 := by
    have h1 : 1 ≤ g ^ 2 := Nat.one_le_pow _ _ hg
    have h2 : 4 * g * ∑ i, e i ≤ 64 * g ^ 4 := by
      calc 4 * g * ∑ i, e i ≤ 4 * g * (16 * g ^ 3) := by gcongr
        _ = 64 * g ^ 4 := by ring
    have h3 : 32 * g ^ 2 * (g ^ 2 - 1) + 32 * g ^ 2 = 32 * g ^ 4 := by
      calc 32 * g ^ 2 * (g ^ 2 - 1) + 32 * g ^ 2 = 32 * g ^ 2 * ((g ^ 2 - 1) + 1) := by ring
        _ = 32 * g ^ 2 * g ^ 2 := by rw [Nat.sub_add_cancel h1]
        _ = 32 * g ^ 4 := by ring
    calc 32 * g ^ 2 * (g ^ 2 - 1) + (32 * g ^ 2 + 4 * g * ∑ i, e i)
        = (32 * g ^ 2 * (g ^ 2 - 1) + 32 * g ^ 2) + 4 * g * ∑ i, e i := by ring
      _ = 32 * g ^ 4 + 4 * g * ∑ i, e i := by rw [h3]
      _ ≤ 32 * g ^ 4 + 64 * g ^ 4 := by gcongr
      _ = 96 * g ^ 4 := by ring
  have hPexp : 256 * g * ν + ∑ i, 32 * νi i * (e i : ℝ) ≤ ((2 ^ 10 * g ^ 3 : ℕ) : ℝ) := by
    push_cast
    have : 256 * (g : ℝ) * ν ≤ 256 * g * (2 * (g : ℝ) ^ 2) := by gcongr
    nlinarith
  calc (10 * g : ℝ) ^ (5 * g) * L ^ (4 * g) * ∏ i, Li i ^ (8 * n i ^ 2 * gi i * d i)
      ≤ (10 * g : ℝ) ^ (5 * g) * (((2 : ℝ) ^ (-116 : ℤ)) ^ (4 * g) * X ^ (32 * g ^ 2) *
          P ^ (256 * g * ν)) *
          (X ^ (4 * g * ∑ i, e i) * P ^ (∑ i, 32 * νi i * (e i : ℝ))) := by
        gcongr
        exact Finset.prod_nonneg fun i _ ↦ pow_nonneg (hLi i).le _
    _ = ((10 * g : ℝ) ^ (5 * g) * ((2 : ℝ) ^ (-116 : ℤ)) ^ (4 * g)) *
          X ^ (32 * g ^ 2 + 4 * g * ∑ i, e i) *
          P ^ (256 * g * ν + ∑ i, 32 * νi i * (e i : ℝ)) := by
        rw [pow_add, rpow_add hP0]; ring
    _ ≤ X ^ (32 * g ^ 2 * (g ^ 2 - 1)) * X ^ (32 * g ^ 2 + 4 * g * ∑ i, e i) *
          P ^ (((2 ^ 10 * g ^ 3 : ℕ) : ℝ)) := by
        gcongr
        exact h10.trans hg5
    _ = X ^ (32 * g ^ 2 * (g ^ 2 - 1) + (32 * g ^ 2 + 4 * g * ∑ i, e i)) *
          P ^ (2 ^ 10 * g ^ 3) := by
        rw [← pow_add, rpow_natCast]
    _ ≤ X ^ (96 * g ^ 4) * P ^ (2 ^ 10 * g ^ 3) := by
        gcongr

end GaudronRemond
