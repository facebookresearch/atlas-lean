/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Characteristic function of the standardized binomial distribution

The characteristic function of a binomial distribution, the affine
transformation rule for characteristic functions, and the key analytic step
in the De Moivre–Laplace limit theorem: the characteristic function of the
standardized binomial distribution converges pointwise to the characteristic
function `exp (-t² / 2)` of the standard normal distribution.

## Source

This formalizes the characteristic-function lemmas of
`v1/Atlas/TheoryOfProbability/code/DeMoivreLaplace.lean`:
`charFun_map_affine`, `charFun_binomial_real`, `exp_taylor2_err`,
`charFun_standardizedBinomial`, and `tendsto_charFun_standardizedBinomial`
(the key analytic step in the v1 proof of `deMoivreLaplace_clt`).
Batch 11 (#321) proved the De Moivre–Laplace limit theorem itself by a
different route (Mathlib's central limit theorem plus Portmanteau) and did
not port any of these lemmas; the limit theorem is not claimed here.

Two proofs differ from v1. The binomial point-mass chain
(`binomial_singleton`, `binomial_singleton_toReal`,
`integral_binomial_eq_sum`) is now in Mathlib
(`ProbabilityTheory.binomial_singleton`,
`ProbabilityTheory.integral_map_cast_binomial`), so
`charFun_binomial_real` is proved from
`ProbabilityTheory.integral_map_cast_binomial` instead of re-porting that
chain. The probability-measure instance for `Bin(ℝ, n, p)` in v1
(`isProbabilityMeasure_Bin_real`) is dropped: it is a direct pushforward
of a probability measure, so the instance is found by `inferInstance`.
The instance for `standardizedBinomial` is kept: typeclass resolution
does not unfold the definition, so without it
`IsProbabilityMeasure (standardizedBinomial n p)` is not found.

## Main results

* `MathlibExt.Probability.CharFunStandardizedBinomial.standardizedBinomial`:
  the law of `(Sₙ − np) / √(np(1−p))` where `Sₙ ~ Binomial(n, p)`.
* `MathlibExt.Probability.CharFunStandardizedBinomial.charFun_map_affine`:
  if `Y = (X − a) / s` then `φ_Y(t) = φ_X(t / s) · exp(−i a t / s)`.
* `MathlibExt.Probability.CharFunStandardizedBinomial.charFun_binomial_real`:
  `φ_{Bin(n, p)}(t) = ((1 − p) + p · e^{it})ⁿ`.
* `MathlibExt.Probability.CharFunStandardizedBinomial.exp_taylor2_err`:
  for `‖z‖ ≤ 1`, `‖e^z − 1 − z − z² / 2‖ ≤ 2 ‖z‖³`.
* `MathlibExt.Probability.CharFunStandardizedBinomial.charFun_standardizedBinomial`:
  the characteristic function of the standardized binomial as a rescaling
  of the characteristic function of `Bin(n, p)`.
* `MathlibExt.Probability.CharFunStandardizedBinomial.tendsto_charFun_standardizedBinomial`:
  for `0 < p < 1` and every `t`, the characteristic function of the
  standardized binomial converges to `exp(−t² / 2)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped unitInterval NNReal Topology Real

namespace MathlibExt.Probability.CharFunStandardizedBinomial

/-- **Standardized binomial distribution.** For a natural number $n$ and $p \in [0, 1]$, the
standardized binomial distribution is the measure on $\mathbb{R}$ given by the law of
$(S_n - np)/\sqrt{np(1-p)}$, where $S_n$ has the binomial distribution with parameters $n$ and
$p$. When $np(1-p) = 0$ the division by $0$ is read as $0$, so the law is the point mass at $0$.

This is the standardized sum appearing in the De Moivre–Laplace limit theorem. -/
noncomputable def standardizedBinomial (n : ℕ) (p : I) : Measure ℝ :=
  Bin(ℝ, n, p).map (fun x : ℝ ↦ (x - ↑n * ↑p) / Real.sqrt (↑n * ↑p * (1 - ↑p)))

/-- The standardized binomial measure is a probability measure (pushforward of a
probability measure under a measurable map). -/
instance isProbabilityMeasure_standardizedBinomial (n : ℕ) (p : I) :
    IsProbabilityMeasure (standardizedBinomial n p) := by
  unfold standardizedBinomial
  infer_instance

/-- **Affine transformation of a characteristic function.** Let $\mu$ be a measure on
$\mathbb{R}$, let $a, s, t \in \mathbb{R}$, and let $\nu$ be the image of $\mu$ under the map
$x \mapsto (x - a)/s$. Then the characteristic functions satisfy
$\varphi_\nu(t) = \varphi_\mu(t s^{-1}) \, e^{-i a t s^{-1}}$. Here $s^{-1}$ and division by $s$
are read as $0$ when $s = 0$, so no hypothesis $s \neq 0$ is needed. -/
theorem charFun_map_affine (μ : Measure ℝ) (a s t : ℝ) :
    charFun (μ.map (fun x => (x - a) / s)) t =
      charFun μ (t * s⁻¹) * Complex.exp (↑(-(a * (t * s⁻¹))) * Complex.I) := by
  have decomp : μ.map (fun x => (x - a) / s) =
      (μ.map (fun x => x + (-a))).map (fun x => s⁻¹ * x) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1; ext x; simp [Function.comp, sub_eq_add_neg, div_eq_mul_inv, mul_comm]
  rw [decomp, charFun_map_mul, charFun_map_add_const]
  congr 1
  · congr 1; ring
  · congr 1
    simp [inner, mul_comm]

/-- **Characteristic function of the real-valued binomial distribution.** For every natural
number $n$, every $p \in [0, 1]$ and every real $t$, the characteristic function
$\varphi_{\mathrm{Bin}(n, p)}$ of the binomial distribution $\mathrm{Bin}(n, p)$, viewed as a
measure on $\mathbb{R}$, satisfies
$\varphi_{\mathrm{Bin}(n, p)}(t) = \left((1 - p) + p e^{it}\right)^n$. -/
theorem charFun_binomial_real (n : ℕ) (p : I) (t : ℝ) :
    charFun Bin(ℝ, n, p) t =
      ((1 - (p : ℝ)) + (p : ℝ) * Complex.exp (↑t * Complex.I)) ^ n := by
  have hsum : ∀ k : ℕ, (n.choose k * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) •
        Complex.exp (t * (k : ℝ) * Complex.I) =
      (n.choose k : ℂ) * (((p : ℝ) : ℂ) * Complex.exp (↑t * Complex.I)) ^ k *
        ((1 - (p : ℝ)) : ℂ) ^ (n - k) := by
    intro k
    rw [Complex.real_smul]
    have hexp : Complex.exp (t * (k : ℝ) * Complex.I) =
        (Complex.exp (↑t * Complex.I)) ^ k := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hexp]
    push_cast
    ring
  rw [charFun_apply_real, integral_map_cast_binomial,
    ← Nat.range_succ_eq_Iic]
  calc ∑ k ∈ Finset.range (n + 1),
          (n.choose k * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) •
            Complex.exp (t * (k : ℝ) * Complex.I)
      = ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℂ) * (((p : ℝ) : ℂ) * Complex.exp (↑t * Complex.I)) ^ k *
            ((1 - (p : ℝ)) : ℂ) ^ (n - k) :=
        Finset.sum_congr rfl (fun k _ => hsum k)
    _ = ((((p : ℝ) : ℂ) * Complex.exp (↑t * Complex.I)) + ((1 - (p : ℝ)) : ℂ)) ^ n := by
        rw [Commute.add_pow (Commute.all _ _)]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ = ((1 - (p : ℝ)) + (p : ℝ) * Complex.exp (↑t * Complex.I)) ^ n := by
        congr 1
        ring

/-- **Second-order Taylor remainder bound for the exponential.** For every complex number $z$
with $|z| \le 1$, the remainder after the degree-2 Taylor polynomial of the exponential
satisfies $|e^z - 1 - z - z^2/2| \le 2|z|^3$. -/
theorem exp_taylor2_err (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - 1 - z - z ^ 2 / 2‖ ≤ 2 * ‖z‖ ^ 3 := by
  have h := Complex.exp_bound hz (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial,
    Nat.cast_one, div_one, zero_add] at h
  have hconv : ‖Complex.exp z - (1 + z + z ^ 2 / ↑2)‖ ≤ ‖z‖ ^ 3 * (↑4 * (↑6 * ↑3)⁻¹) := by
    convert h using 2; push_cast; ring
  calc ‖Complex.exp z - 1 - z - z ^ 2 / 2‖
      = ‖Complex.exp z - (1 + z + z ^ 2 / ↑2)‖ := by congr 1; ring
    _ ≤ ‖z‖ ^ 3 * (↑4 * (↑6 * ↑3)⁻¹) := hconv
    _ ≤ ‖z‖ ^ 3 * 2 := by gcongr; norm_num
    _ = 2 * ‖z‖ ^ 3 := by ring

/-- **Characteristic function of the standardized binomial.** For every natural number $n$,
every $p \in [0, 1]$ and every real $t$, put $s = \sqrt{np(1-p)}$, with $s^{-1}$ read as $0$ when
$s = 0$. Let $\psi$ be the characteristic function of the binomial distribution
$\mathrm{Bin}(n, p)$ viewed as a measure on $\mathbb{R}$, and $\varphi$ that of the standardized
binomial distribution with parameters $n$ and $p$. Then
$\varphi(t) = \psi(t s^{-1}) \, e^{-i n p t s^{-1}}$. -/
theorem charFun_standardizedBinomial (n : ℕ) (p : I) (t : ℝ) :
    let s := Real.sqrt (↑n * ↑p * (1 - ↑p))
    charFun (standardizedBinomial n p) t =
      charFun Bin(ℝ, n, p) (t * s⁻¹) *
        Complex.exp (↑(-(↑n * (↑p : ℝ) * (t * s⁻¹))) * Complex.I) := by
  intro s
  unfold standardizedBinomial
  exact charFun_map_affine _ _ _ _

/-- **Convergence of characteristic functions in De Moivre–Laplace.** Let $0 < p < 1$ and
$t \in \mathbb{R}$. As $n \to \infty$, the characteristic function of the standardized binomial
distribution with parameters $n$ and $p$, evaluated at $t$, converges to $e^{-t^2/2}$, the
value at $t$ of the characteristic function of the standard normal distribution.

This is the key analytic step in proving the De Moivre–Laplace theorem via Lévy's continuity
theorem. -/
theorem tendsto_charFun_standardizedBinomial (p : I) (hp₀ : (0 : ℝ) < p) (hp₁ : (p : ℝ) < 1)
    (t : ℝ) :
    Tendsto (fun n ↦ charFun (standardizedBinomial n p) t) atTop
      (𝓝 (Complex.exp (-(t ^ 2 / 2)))) := by
  set pp := (p : ℝ) with hpp
  set qq := 1 - pp with hqq
  have hqq_pos : 0 < qq := by linarith
  have hpp_pos : 0 < pp := hp₀
  have hpq_pos : 0 < pp * qq := mul_pos hpp_pos hqq_pos
  set B : ℕ → ℂ := fun n =>
    let s := Real.sqrt (↑n * pp * qq)
    let u := t * s⁻¹
    ↑qq * Complex.exp (↑(-(pp * u)) * Complex.I) +
      ↑pp * Complex.exp (↑(qq * u) * Complex.I)
  suffices h_conv : Tendsto (fun n => (B n) ^ n) atTop (𝓝 (Complex.exp (-(t ^ 2 / 2)))) by
    apply h_conv.congr
    intro n
    simp only [B]
    rw [charFun_standardizedBinomial, charFun_binomial_real]
    set s := Real.sqrt (↑n * pp * qq)
    set u := t * s⁻¹
    show (↑qq * Complex.exp (↑(-(pp * u)) * Complex.I) + ↑pp * Complex.exp (↑(qq * u) * Complex.I)) ^ n =
      ((1 - pp) + pp * Complex.exp (↑u * Complex.I)) ^ n *
        Complex.exp (↑(-(↑n * pp * u)) * Complex.I)
    rw [show (↑(-(↑n * pp * u)) : ℂ) * Complex.I = ↑n * (↑(-(pp * u)) * Complex.I) by push_cast; ring]
    rw [Complex.exp_nat_mul, ← mul_pow]
    congr 1
    rw [add_mul]
    have hqq_cast : (qq : ℂ) = 1 - (pp : ℂ) := by
      simp only [hqq]; push_cast; ring
    congr 1
    · rw [hqq_cast]
    · rw [mul_assoc, ← Complex.exp_add]
      congr 1
      have : qq * u = u + -(pp * u) := by rw [hqq]; ring
      rw [this]; push_cast; ring_nf
  set z₀ : ℂ := -((↑t : ℂ) ^ 2 / 2)
  apply Complex.tendsto_pow_exp_of_isLittleO_sub_add_div z₀
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  set K := 2 * |t| ^ 3 / (pp * qq) ^ (3/2 : ℝ)
  have hN_bound : ∀ᶠ (n : ℕ) in atTop, |t| / Real.sqrt (↑n * (pp * qq)) ≤ 1 := by
    filter_upwards [Filter.eventually_ge_atTop (⌈t ^ 2 / (pp * qq)⌉.toNat + 1)] with n hn
    rw [div_le_one (Real.sqrt_pos.mpr (mul_pos (Nat.cast_pos.mpr (by omega)) hpq_pos))]
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    calc t ^ 2 ≤ ⌈t ^ 2 / (pp * qq)⌉ * (pp * qq) := by
          rw [← div_le_iff₀ hpq_pos]; exact Int.le_ceil _
        _ ≤ ↑n * (pp * qq) := by
          gcongr
          have : ⌈t ^ 2 / (pp * qq)⌉.toNat ≤ n := by omega
          calc (⌈t ^ 2 / (pp * qq)⌉ : ℝ)
              ≤ ↑(⌈t ^ 2 / (pp * qq)⌉.toNat : ℤ) := by exact_mod_cast Int.self_le_toNat _
            _ ≤ ↑n := by exact_mod_cast this
  have hK_bound : ∀ᶠ (n : ℕ) in atTop, K / Real.sqrt n ≤ ε := by
    filter_upwards [Filter.eventually_ge_atTop (⌈(K / ε) ^ 2⌉.toNat + 1)] with n hn
    have hn_pos : 0 < n := by omega
    rw [div_le_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn_pos))]
    have h1 : (K / ε) ^ 2 ≤ ↑n := by
      have : ⌈(K / ε) ^ 2⌉.toNat ≤ n := by omega
      calc (K / ε) ^ 2 ≤ ↑⌈(K / ε) ^ 2⌉ := Int.le_ceil _
        _ ≤ ↑(⌈(K / ε) ^ 2⌉.toNat) := by exact_mod_cast Int.self_le_toNat _
        _ ≤ ↑n := by exact_mod_cast this
    calc K ≤ K / ε * ε := by rw [div_mul_cancel₀]; exact ne_of_gt hε
      _ ≤ Real.sqrt ↑n * ε := by
          gcongr; exact Real.le_sqrt_of_sq_le h1
      _ = ε * Real.sqrt ↑n := mul_comm _ _
  filter_upwards [hN_bound, hK_bound, Filter.eventually_ge_atTop 1] with n hsmall hK_small hn_pos
  set sig := Real.sqrt (↑n * pp * qq) with hsig_def
  set u := t * sig⁻¹ with hu_def
  set a : ℂ := ↑(-(pp * u)) * Complex.I with ha_def
  set b : ℂ := ↑(qq * u) * Complex.I with hb_def
  set R_a := Complex.exp a - 1 - a - a ^ 2 / 2
  set R_b := Complex.exp b - 1 - b - b ^ 2 / 2
  have hB_unfold : B n = ↑qq * Complex.exp a + ↑pp * Complex.exp b := by
    simp only [B, a, b, sig, u]
  have hqq_pp : (↑qq : ℂ) + ↑pp = 1 := by
    push_cast [hqq]; ring
  have hlin : (↑qq : ℂ) * a + ↑pp * b = 0 := by
    simp only [a, b]; push_cast; simp [hqq]; ring
  have hn_pos' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have hsig_pos : 0 < sig := Real.sqrt_pos.mpr (by positivity)
  have hsig_sq : sig ^ 2 = ↑n * pp * qq := Real.sq_sqrt (by positivity)
  have hquad : (↑qq : ℂ) * (a ^ 2 / 2) + ↑pp * (b ^ 2 / 2) = z₀ / ↑↑n := by
    have ha2 : a ^ 2 = -(↑(pp * u) : ℂ) ^ 2 := by
      simp only [a]; rw [mul_pow, Complex.I_sq]; push_cast; ring
    have hb2 : b ^ 2 = -(↑(qq * u) : ℂ) ^ 2 := by
      simp only [b]; rw [mul_pow, Complex.I_sq]; push_cast; ring
    rw [ha2, hb2]
    have h : (qq * (-(pp * u) ^ 2 / 2) + pp * (-(qq * u) ^ 2 / 2) : ℝ) = -(t ^ 2 / 2) / ↑n := by
      show qq * (-(pp * (t * sig⁻¹)) ^ 2 / 2) + pp * (-(qq * (t * sig⁻¹)) ^ 2 / 2) = -(t ^ 2 / 2) / ↑n
      rw [hqq]; rw [hqq] at hsig_sq; field_simp; rw [hsig_sq]; ring
    have := congr_arg (fun (x : ℝ) => (x : ℂ)) h
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow,
               Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat] at this
    convert this using 1
    push_cast
    ring
  have hBR : B n - (1 + z₀ / ↑↑n) = ↑qq * R_a + ↑pp * R_b := by
    have hexp_a : Complex.exp a = 1 + a + a ^ 2 / 2 + R_a := by simp [R_a]
    have hexp_b : Complex.exp b = 1 + b + b ^ 2 / 2 + R_b := by simp [R_b]
    rw [hB_unfold, hexp_a, hexp_b]
    have : ↑qq * (1 + a + a ^ 2 / 2 + R_a) + ↑pp * (1 + b + b ^ 2 / 2 + R_b) - (1 + z₀ / ↑↑n) =
      (↑qq + ↑pp - 1) + (↑qq * a + ↑pp * b) + (↑qq * (a ^ 2 / 2) + ↑pp * (b ^ 2 / 2) - z₀ / ↑↑n) +
      (↑qq * R_a + ↑pp * R_b) := by ring
    rw [this, hqq_pp, hlin, hquad]; ring
  have hsmall_sig : |t| / sig ≤ 1 := by
    rwa [show sig = Real.sqrt (↑n * (pp * qq)) from by rw [hsig_def]; ring_nf]
  have hu_abs : |u| = |t| / sig := by
    rw [hu_def, abs_mul, abs_inv, abs_of_pos hsig_pos, div_eq_mul_inv]
  have ha_norm : ‖a‖ ≤ 1 := by
    simp only [a, Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    calc |-(pp * u)| = pp * |u| := by rw [abs_neg, abs_mul, abs_of_pos hpp_pos]
      _ = pp * (|t| / sig) := by rw [hu_abs]
      _ ≤ 1 * 1 := by
          apply mul_le_mul (le_of_lt hp₁) hsmall_sig (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (by linarith)
      _ = 1 := one_mul 1
  have hb_norm : ‖b‖ ≤ 1 := by
    simp only [b, Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    calc |qq * u| = qq * |u| := by rw [abs_mul, abs_of_pos hqq_pos]
      _ = qq * (|t| / sig) := by rw [hu_abs]
      _ ≤ 1 * 1 := by
          apply mul_le_mul (by linarith) hsmall_sig (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (by linarith)
      _ = 1 := one_mul 1
  have hRa_bound := exp_taylor2_err a ha_norm
  have hRb_bound := exp_taylor2_err b hb_norm
  have ha_le : ‖a‖ ≤ |t| / sig := by
    simp only [a, Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    calc |-(pp * u)| = pp * |u| := by rw [abs_neg, abs_mul, abs_of_pos hpp_pos]
      _ = pp * (|t| / sig) := by rw [hu_abs]
      _ ≤ 1 * (|t| / sig) := by
          apply mul_le_mul_of_nonneg_right (le_of_lt hp₁) (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      _ = |t| / sig := one_mul _
  have hb_le : ‖b‖ ≤ |t| / sig := by
    simp only [b, Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    calc |qq * u| = qq * |u| := by rw [abs_mul, abs_of_pos hqq_pos]
      _ = qq * (|t| / sig) := by rw [hu_abs]
      _ ≤ 1 * (|t| / sig) := by
          apply mul_le_mul_of_nonneg_right (by linarith) (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      _ = |t| / sig := one_mul _
  have hn_norm : ‖(1 : ℂ) / ↑↑n‖ = 1 / ↑n := by
    rw [one_div, norm_inv, Complex.norm_natCast]
    simp
  rw [hBR, hn_norm]
  calc ‖↑qq * R_a + ↑pp * R_b‖
      ≤ ‖↑qq * R_a‖ + ‖↑pp * R_b‖ := norm_add_le _ _
    _ = qq * ‖R_a‖ + pp * ‖R_b‖ := by
        rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hqq_pos, abs_of_pos hpp_pos]
    _ ≤ qq * (2 * ‖a‖ ^ 3) + pp * (2 * ‖b‖ ^ 3) := by
        gcongr
    _ ≤ qq * (2 * (|t| / sig) ^ 3) + pp * (2 * (|t| / sig) ^ 3) := by
        gcongr
    _ = 2 * (|t| / sig) ^ 3 := by ring_nf; linarith
    _ ≤ ε * (1 / ↑n) := by
        have hn_pos_r : (0 : ℝ) < ↑n := hn_pos'
        rw [div_pow, mul_div, mul_one_div, div_le_div_iff₀ (pow_pos hsig_pos 3) hn_pos_r]
        rw [show sig ^ 3 = sig * sig ^ 2 from by ring, hsig_sq]
        have hK_le : K ≤ ε * Real.sqrt ↑n := by
          calc K = K / Real.sqrt ↑n * Real.sqrt ↑n := by
                rw [div_mul_cancel₀]; exact ne_of_gt (Real.sqrt_pos.mpr hn_pos_r)
            _ ≤ ε * Real.sqrt ↑n := by gcongr
        have h2t3 : 2 * |t| ^ 3 = K * (pp * qq) ^ (3/2 : ℝ) := by
          simp only [K]; field_simp
        have hrpow : (pp * qq) ^ (3/2 : ℝ) = Real.sqrt (pp * qq) * (pp * qq) := by
          rw [Real.sqrt_eq_rpow, show (3 : ℝ)/2 = 1/2 + 1 from by norm_num,
              Real.rpow_add hpq_pos, Real.rpow_one]
        have hsig_eq : sig = Real.sqrt (↑n * (pp * qq)) := by
          rw [← Real.sqrt_sq hsig_pos.le, hsig_sq]; ring_nf
        have hsqrt_prod : Real.sqrt ↑n * Real.sqrt (pp * qq) = sig := by
          rw [hsig_eq, ← Real.sqrt_mul hn_pos_r.le]
        have hkey : Real.sqrt ↑n * (pp * qq) ^ (3/2 : ℝ) * ↑n = sig * (↑n * pp * qq) := by
          rw [hrpow, show Real.sqrt ↑n * (Real.sqrt (pp * qq) * (pp * qq)) * ↑n =
               (Real.sqrt ↑n * Real.sqrt (pp * qq)) * (pp * qq) * ↑n from by ring,
               hsqrt_prod]; ring
        calc 2 * |t| ^ 3 * ↑n
            = K * (pp * qq) ^ (3/2 : ℝ) * ↑n := by rw [h2t3]
          _ ≤ (ε * Real.sqrt ↑n) * (pp * qq) ^ (3/2 : ℝ) * ↑n := by gcongr
          _ = ε * (Real.sqrt ↑n * (pp * qq) ^ (3/2 : ℝ) * ↑n) := by ring
          _ = ε * (sig * (↑n * pp * qq)) := by rw [hkey]

end MathlibExt.Probability.CharFunStandardizedBinomial
