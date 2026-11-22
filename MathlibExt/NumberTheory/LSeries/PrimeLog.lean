/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.LSeries.Nonvanishing

@[expose] public section

/-!
# Meromorphic continuation of the prime logarithmic Dirichlet series

This module formalizes NumberTheoryI Lemma 16.11: for the prime logarithmic
series `Φ(s) = ∑_p log p / p ^ s`, the difference `Φ(s) - 1 / (s - 1)` admits a
single meromorphic continuation to `Re s > 1 / 2` which is holomorphic on the
closed half-plane `Re s ≥ 1`.

The proof follows the classical route.  Writing the von Mangoldt L-series over
prime powers splits off the prime terms from the higher prime powers:
`L(Λ, s) = Φ(s) + C(s)` on `Re s > 1`, where the correction series `C(s)`
already converges for `Re s > 1 / 2`.  Since `L(Λ, s) = -ζ'(s) / ζ(s)` and
`ζ(s) = (s - 1)⁻¹ * ζ₁(s)` with `ζ₁` entire and nonvanishing on `Re s ≥ 1`,
the canonical continuation is `-ζ₁'(s) / ζ₁(s) - C(s)`.

## Main definitions

* `Nat.Primes.logDirichletSeries`: the prime sum `Φ(s)`.
* `Nat.Primes.logDirichletCorrectionTerm`: one higher-prime-power summand.
* `Nat.Primes.logDirichletCorrection`: the correction series `C(s)`.
* `Nat.Primes.logDirichletContinuation`: the canonical continuation.

## Main results

* `Nat.Primes.logDirichletCorrection_analyticOn`: `C` is analytic on `Re > 1/2`.
* `Nat.Primes.logDirichlet_vonMangoldt_split`: `L(Λ, s) = Φ(s) + C(s)`.
* `Nat.Primes.logDirichletSeries_eq`: `Φ` via the zeta logarithmic derivative.
* `Nat.Primes.logDirichletContinuation_meromorphic`: meromorphicity on `Re > 1/2`.
* `Nat.Primes.logDirichletContinuation_analyticOn`: analyticity on `Re ≥ 1`.
* `Nat.Primes.logDirichletContinuation_agree`: agreement with `Φ - 1/(·-1)`.
* `Nat.Primes.logDirichlet_meromorphicContinuation`: the combined endpoint.
-/

open scoped LSeries.notation

namespace Nat.Primes

/-- **Prime logarithmic Dirichlet series.** For a complex number $s$, the prime logarithmic
Dirichlet series is $\Phi(s) = \sum_{p} \frac{\log p}{p^s}$, summed over all primes $p$ (the sum
is taken to be $0$ where the family is not summable). -/
noncomputable def logDirichletSeries (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, (Real.log ((p : ℕ) : ℝ) : ℂ) / (((p : ℕ)) : ℂ) ^ s

/-- **Summand of the prime-power correction series.** For a prime $p$, a natural number $k$ and a
complex number $s$, the correction summand is $\frac{\log p}{(p^{k+2})^s}$, the term of the
prime-power correction series that belongs to the prime power $p^{k+2}$. -/
noncomputable def logDirichletCorrectionTerm (p : Nat.Primes) (k : ℕ) (s : ℂ) : ℂ :=
  (Real.log ((p : ℕ) : ℝ) : ℂ) / (Nat.cast ((p : ℕ) ^ (k + 2)) : ℂ) ^ s

/-- **Prime-power correction series.** For a complex number $s$, the prime-power correction series
is $C(s) = \sum_{(p, k)} \frac{\log p}{(p^{k+2})^s}$, summed over all pairs of a prime $p$ and a
natural number $k \ge 0$ (the sum is taken to be $0$ where the family is not summable). -/
noncomputable def logDirichletCorrection (s : ℂ) : ℂ :=
  ∑' x : Nat.Primes × ℕ, logDirichletCorrectionTerm x.1 x.2 s

/-- **The canonical prime logarithmic continuation.** For a complex number $s$, the prime
logarithmic continuation is $G(s) = -\frac{\zeta_1'(s)}{\zeta_1(s)} - C(s)$, where $\zeta_1$ is
the entire function with $\zeta_1(s) = (s - 1)\zeta(s)$ for $s \ne 1$ and $\zeta_1(1) = 1$, the
quotient is taken to be $0$ where $\zeta_1(s) = 0$, and $C$ is the prime-power correction series.

This function continues $\Phi(s) - \frac{1}{s-1}$ from $\operatorname{Re} s > 1$ to a meromorphic
function on $\operatorname{Re} s > 1/2$, where $\Phi$ is the prime logarithmic Dirichlet series. -/
noncomputable def logDirichletContinuation (s : ℂ) : ℂ :=
  -(deriv riemannZeta₁ s / riemannZeta₁ s) - logDirichletCorrection s

/-- The prime factor of the correction majorant is summable when `σ₀ > 1 / 2`. -/
private lemma summable_log_mul_rpow {σ₀ : ℝ} (hσ : 1 / 2 < σ₀) :
    Summable
      (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ) *
        ((((p : ℕ)) : ℝ) ^ (-(2 * σ₀)))) := by
  have hε : (0 : ℝ) < (2 * σ₀ - 1) / 2 := by linarith
  set ε : ℝ := (2 * σ₀ - 1) / 2 with hεdef
  have hsum : Summable
      (fun p : Nat.Primes => (1 / ε : ℝ) * ((((p : ℕ)) : ℝ) ^ (-(1 + ε)))) :=
    Summable.mul_left (1 / ε)
      ((Nat.Primes.summable_rpow (r := -(1 + ε))).mpr (by linarith))
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hsum
  · have h1 : (1 : ℝ) ≤ (((p : ℕ)) : ℝ) := by
      have h2 : (2 : ℝ) ≤ (((p : ℕ)) : ℝ) := by
        exact_mod_cast Nat.Prime.two_le p.prop
      linarith
    exact mul_nonneg (Real.log_nonneg h1)
      (Real.rpow_nonneg (by linarith) _)
  · have h2 : (2 : ℝ) ≤ (((p : ℕ)) : ℝ) := by
      exact_mod_cast Nat.Prime.two_le p.prop
    have hpos : (0 : ℝ) < (((p : ℕ)) : ℝ) := by linarith
    have hplog : Real.log (((p : ℕ)) : ℝ) ≤ ((((p : ℕ)) : ℝ) ^ ε / ε) :=
      Real.log_le_rpow_div (by linarith) hε
    calc Real.log _ * _ ^ (-(2 * σ₀))
        ≤ (((((p : ℕ)) : ℝ) ^ ε / ε)) * ((((p : ℕ)) : ℝ) ^ (-(2 * σ₀))) :=
          mul_le_mul_of_nonneg_right hplog (Real.rpow_nonneg (le_of_lt hpos) _)
      _ = (1 / ε) * (((((p : ℕ)) : ℝ) ^ ε) * ((((p : ℕ)) : ℝ) ^ (-(2 * σ₀)))) := by
          ring
      _ = (1 / ε) * ((((p : ℕ)) : ℝ) ^ (-(1 + ε))) := by
          have hex : ε + -(2 * σ₀) = -(1 + ε) := by
            rw [hεdef]
            ring
          rw [← Real.rpow_add hpos, hex]

/-- The uniform majorant for the correction series is summable when `σ₀ > 1 / 2`. -/
private lemma summable_correctionMajorant {σ₀ : ℝ} (hσ : 1 / 2 < σ₀) :
    Summable
      (fun x : Nat.Primes × ℕ => Real.log (((x.1 : ℕ)) : ℝ) *
        ((((x.1 : ℕ)) : ℝ) ^ (-(((x.2 + 2 : ℕ)) : ℝ) * σ₀))) := by
  have hσpos : (0 : ℝ) < σ₀ := by linarith
  set q : ℝ := (2 : ℝ) ^ (-σ₀) with hqdef
  have hqnn : 0 ≤ q := by
    rw [hqdef]
    exact Real.rpow_nonneg (by norm_num) _
  have h2σ : (1 : ℝ) < (2 : ℝ) ^ σ₀ := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hσpos
    rwa [Real.rpow_zero] at h
  have hq1 : q < 1 := by
    rw [hqdef, Real.rpow_neg (by norm_num)]
    exact inv_lt_one_of_one_lt₀ h2σ
  have hw : Summable (fun k : ℕ => q ^ k) := summable_geometric_of_lt_one hqnn hq1
  have hv : Summable
      (fun p : Nat.Primes => Real.log (((p : ℕ)) : ℝ) *
        ((((p : ℕ)) : ℝ) ^ (-(2 * σ₀)))) :=
    summable_log_mul_rpow hσ
  have hprod := hv.mul_of_nonneg hw
    (fun p => mul_nonneg (Real.log_nonneg (by
      have h2 : (2 : ℝ) ≤ (((p : ℕ)) : ℝ) := by
        exact_mod_cast Nat.Prime.two_le p.prop
      linarith)) (Real.rpow_nonneg (by
      have h2 : (2 : ℝ) ≤ (((p : ℕ)) : ℝ) := by
        exact_mod_cast Nat.Prime.two_le p.prop
      linarith) _))
    (fun k => pow_nonneg hqnn _)
  refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hprod
  · obtain ⟨p, k⟩ := x
    have h2 : (2 : ℝ) ≤ (((p : ℕ)) : ℝ) := by
      exact_mod_cast Nat.Prime.two_le p.prop
    exact mul_nonneg (Real.log_nonneg (by linarith)) (Real.rpow_nonneg (by linarith) _)
  · obtain ⟨p, k⟩ := x
    have hp2 : (2 : ℝ) ≤ (((p : ℕ)) : ℝ) := by
      exact_mod_cast Nat.Prime.two_le p.prop
    have hppos : (0 : ℝ) < (((p : ℕ)) : ℝ) := by linarith
    have hplog : 0 ≤ Real.log (((p : ℕ)) : ℝ) := Real.log_nonneg (by linarith)
    have hexp : (-((((k + 2 : ℕ))) : ℝ)) * σ₀ = -(2 * σ₀) + (k : ℝ) * (-σ₀) := by
      push_cast
      ring
    have hbase : ((((p : ℕ)) : ℝ) ^ (-σ₀)) ≤ q := by
      have h1 : ((((p : ℕ)) : ℝ) ^ (-σ₀)) = ((((p : ℕ)) : ℝ) ^ σ₀)⁻¹ :=
        Real.rpow_neg (le_of_lt hppos) _
      have h2 : q = (((2 : ℝ) ^ σ₀))⁻¹ := by
        rw [hqdef, Real.rpow_neg (by norm_num)]
      rw [h1, h2]
      exact (inv_le_inv₀ (Real.rpow_pos_of_pos hppos _)
        (Real.rpow_pos_of_pos (by norm_num) _)).mpr
        (Real.rpow_le_rpow (by norm_num) hp2 (le_of_lt hσpos))
    have hnpow : ((((p : ℕ)) : ℝ) ^ ((k : ℝ) * (-σ₀))) =
        (((((p : ℕ)) : ℝ) ^ (-σ₀)) ^ k) := by
      have hex : (k : ℝ) * (-σ₀) = (-σ₀) * (k : ℝ) := by ring
      rw [hex, Real.rpow_mul (le_of_lt hppos), Real.rpow_natCast]
    change Real.log _ * _ ^ _ ≤ (Real.log _ * _ ^ _) * q ^ k
    calc Real.log (((p : ℕ)) : ℝ) * ((((p : ℕ)) : ℝ) ^ (-(((k + 2 : ℕ)) : ℝ) * σ₀))
        = ((Real.log (((p : ℕ)) : ℝ)) * ((((p : ℕ)) : ℝ) ^ (-(2 * σ₀)))) *
          ((((p : ℕ)) : ℝ) ^ ((k : ℝ) * (-σ₀))) := by
          rw [hexp, Real.rpow_add hppos]
          ring
      _ ≤ ((Real.log (((p : ℕ)) : ℝ)) * ((((p : ℕ)) : ℝ) ^ (-(2 * σ₀)))) * q ^ k := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hplog
            (Real.rpow_nonneg (le_of_lt hppos) _))
          rw [hnpow]
          exact pow_le_pow_left₀ (Real.rpow_nonneg (le_of_lt hppos) _) hbase k

/-- Norm bound for one correction summand, uniform for `σ₀ ≤ w.re`. -/
private lemma norm_correctionTerm_le (p : Nat.Primes) (k : ℕ) (w : ℂ) (σ₀ : ℝ)
    (hw : σ₀ ≤ w.re) :
    ‖logDirichletCorrectionTerm p k w‖
      ≤ Real.log (((p : ℕ)) : ℝ) *
          ((((p : ℕ)) : ℝ) ^ (-((((k + 2 : ℕ))) : ℝ) * σ₀)) := by
  have h2 : (2 : ℝ) ≤ (((p : ℕ)) : ℝ) := by
    exact_mod_cast Nat.Prime.two_le p.prop
  have hlognn : 0 ≤ Real.log (((p : ℕ)) : ℝ) := Real.log_nonneg (by linarith)
  have hN1 : (1 : ℕ) ≤ (p : ℕ) ^ (k + 2) :=
    Nat.one_le_pow _ _ (Nat.Prime.pos p.prop)
  have hNpos : (0 : ℝ) < (((p : ℕ) ^ (k + 2) : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hN1
  have h1le : (1 : ℝ) ≤ (((p : ℕ) ^ (k + 2) : ℕ) : ℝ) := by
    exact_mod_cast hN1
  have hbase : (Nat.cast ((p : ℕ) ^ (k + 2)) : ℂ)
      = ((((p : ℕ) ^ (k + 2) : ℕ) : ℝ) : ℂ) :=
    (Complex.ofReal_natCast _).symm
  have hNσ : ((((p : ℕ) ^ (k + 2) : ℕ) : ℝ)) ^ σ₀
      = ((((p : ℕ)) : ℝ) ^ (((((k + 2 : ℕ))) : ℝ) * σ₀)) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  have hle : ((((p : ℕ) ^ (k + 2) : ℕ) : ℝ)) ^ σ₀
      ≤ ((((p : ℕ) ^ (k + 2) : ℕ) : ℝ)) ^ (w.re) :=
    Real.rpow_le_rpow_of_exponent_le h1le hw
  change ‖(Real.log (((p : ℕ)) : ℝ) : ℂ) /
      (Nat.cast ((p : ℕ) ^ (k + 2)) : ℂ) ^ w‖ ≤ _
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlognn, hbase,
    Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
  calc Real.log (((p : ℕ)) : ℝ) / ((((p : ℕ) ^ (k + 2) : ℕ) : ℝ)) ^ (w.re)
      ≤ Real.log (((p : ℕ)) : ℝ) / ((((p : ℕ) ^ (k + 2) : ℕ) : ℝ)) ^ σ₀ :=
        div_le_div_of_nonneg_left hlognn (Real.rpow_pos_of_pos hNpos _) hle
    _ = Real.log (((p : ℕ)) : ℝ) *
        ((((p : ℕ)) : ℝ) ^ (-((((k + 2 : ℕ))) : ℝ) * σ₀)) := by
        rw [hNσ, div_eq_mul_inv, ← Real.rpow_neg (by linarith), neg_mul]

/-- Each correction summand is an entire function of `w`. -/
private lemma differentiable_correctionTerm (p : Nat.Primes) (k : ℕ) :
    Differentiable ℂ (fun w => logDirichletCorrectionTerm p k w) := by
  have hN0 : (Nat.cast ((p : ℕ) ^ (k + 2)) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero _ (ne_of_gt (Nat.Prime.pos p.prop))
  change Differentiable ℂ
    (fun w => (Real.log (((p : ℕ)) : ℝ) : ℂ) / (Nat.cast ((p : ℕ) ^ (k + 2)) : ℂ) ^ w)
  refine Differentiable.div (differentiable_const _) ?_ ?_
  · exact differentiable_id.const_cpow (Or.inl hN0)
  · intro w
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hN0)

/-- The correction series is summable wherever `1 / 2 < s.re`. -/
private lemma summable_logDirichletCorrectionTerm {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun x : Nat.Primes × ℕ => logDirichletCorrectionTerm x.1 x.2 s) := by
  have hsum := summable_correctionMajorant (σ₀ := s.re) hs
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_) hsum
  obtain ⟨p, k⟩ := x
  exact norm_correctionTerm_le p k s s.re le_rfl

/-- **Analyticity of the prime-power correction series.** The prime-power correction series
$C(s) = \sum_{(p, k)} \frac{\log p}{(p^{k+2})^s}$, summed over all primes $p$ and natural
numbers $k \ge 0$, is analytic at every point of the open half-plane
$\{s \in \mathbb{C} : \operatorname{Re} s > 1/2\}$. -/
theorem logDirichletCorrection_analyticOn :
    AnalyticOnNhd ℂ logDirichletCorrection {s | 1 / 2 < s.re} := by
  intro s₀ hs₀
  have hs₀' : (1 / 2 : ℝ) < s₀.re := hs₀
  set σ₀ : ℝ := (1 / 2 + s₀.re) / 2 with hσ₀def
  have hσ : (1 / 2 : ℝ) < σ₀ := by linarith
  have hσs : σ₀ < s₀.re := by linarith
  have hUopen : IsOpen {w : ℂ | σ₀ < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ logDirichletCorrection {w : ℂ | σ₀ < w.re} := by
    have hbase := Complex.differentiableOn_tsum_of_summable_norm
      (F := fun x : Nat.Primes × ℕ => logDirichletCorrectionTerm x.1 x.2)
      (U := {w : ℂ | σ₀ < w.re}) (summable_correctionMajorant hσ)
      (fun x => (differentiable_correctionTerm x.1 x.2).differentiableOn)
      hUopen
      (fun x w hw => norm_correctionTerm_le x.1 x.2 w σ₀
        (le_of_lt (show σ₀ < w.re from hw)))
    exact hbase
  have hanal := hdiff.analyticOnNhd hUopen
  exact hanal s₀ hσs

/-- **Splitting the von Mangoldt L-series over prime powers.** For every complex number $s$
with $\operatorname{Re} s > 1$, the L-series $\sum_{n \ge 1} \Lambda(n) n^{-s}$ of the von
Mangoldt function $\Lambda$ equals $\Phi(s) + C(s)$, where $\Phi(s) = \sum_p \log p / p^s$ is
the prime logarithmic Dirichlet series, summed over all primes $p$, and
$C(s) = \sum_{(p, k)} \log p / (p^{k+2})^s$ is the higher-prime-power correction series, summed
over all pairs of a prime $p$ and a natural number $k \ge 0$. -/
theorem logDirichlet_vonMangoldt_split {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗ArithmeticFunction.vonMangoldt s
      = logDirichletSeries s + logDirichletCorrection s := by
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hsup : Function.support (LSeries.term ↗ArithmeticFunction.vonMangoldt s)
      ⊆ {n | IsPrimePow n} := by
    intro n hn
    rw [Function.mem_support] at hn
    change IsPrimePow n
    by_contra hcon
    apply hn
    by_cases h0 : n = 0
    · simp [LSeries.term, h0]
    · have hΛ : ((((ArithmeticFunction.vonMangoldt n : ℝ))) : ℂ) = 0 := by
        have h0' : ArithmeticFunction.vonMangoldt n = 0 :=
          ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hcon
        rw [h0']
        rfl
      rw [LSeries.term_of_ne_zero h0, hΛ, zero_div]
  have hsplit := tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers
    (f := LSeries.term ↗ArithmeticFunction.vonMangoldt s) hsum hsup
  have hcorr := summable_logDirichletCorrectionTerm (s := s) (by linarith : (1 / 2 : ℝ) < s.re)
  have hterm : ∀ p : Nat.Primes, LSeries.term ↗ArithmeticFunction.vonMangoldt s ↑p
      = (Real.log ((((p : ℕ))) : ℝ) : ℂ) / (((p : ℕ)) : ℂ) ^ s := by
    intro p
    rw [LSeries.term_of_ne_zero p.prop.ne_zero]
    congr 1
    show ((((ArithmeticFunction.vonMangoldt ↑p : ℝ))) : ℂ) = _
    rw [ArithmeticFunction.vonMangoldt_apply_prime p.prop]
  have hterm2 : ∀ p : Nat.Primes, ∀ k : ℕ,
      LSeries.term ↗ArithmeticFunction.vonMangoldt s (↑p ^ (k + 2))
        = logDirichletCorrectionTerm p k s := by
    intro p k
    have hN : (↑p : ℕ) ^ (k + 2) ≠ 0 := pow_ne_zero _ p.prop.ne_zero
    rw [LSeries.term_of_ne_zero hN]
    change (↗ArithmeticFunction.vonMangoldt) _ / _ = logDirichletCorrectionTerm p k s
    unfold logDirichletCorrectionTerm
    congr 1
    change ((((ArithmeticFunction.vonMangoldt (↑p ^ (k + 2)) : ℝ))) : ℂ) = _
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : k + 2 ≠ 0),
      ArithmeticFunction.vonMangoldt_apply_prime p.prop]
  change ∑' n, LSeries.term ↗ArithmeticFunction.vonMangoldt s n = _ + _
  rw [hsplit]
  congr 1
  · exact tsum_congr fun p => hterm p
  · change ∑' (p : Nat.Primes) (k : ℕ),
        LSeries.term ↗ArithmeticFunction.vonMangoldt s (↑p ^ (k + 2))
        = ∑' x : Nat.Primes × ℕ, logDirichletCorrectionTerm x.1 x.2 s
    rw [Summable.tsum_prod hcorr]
    exact tsum_congr fun p => tsum_congr fun k => hterm2 p k

/-- **Prime logarithmic series via the logarithmic derivative of zeta.** For every complex number
$s$ with $\operatorname{Re} s > 1$, $\Phi(s) = -\frac{\zeta'(s)}{\zeta(s)} - C(s)$, where $\Phi$
is the prime logarithmic Dirichlet series, $\zeta$ is the Riemann zeta function and $C$ is the
prime-power correction series. -/
theorem logDirichletSeries_eq {s : ℂ} (hs : 1 < s.re) :
    logDirichletSeries s
      = -deriv riemannZeta s / riemannZeta s - logDirichletCorrection s := by
  have hΛ := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hsplit := logDirichlet_vonMangoldt_split hs
  have hcomb : logDirichletSeries s + logDirichletCorrection s
      = -deriv riemannZeta s / riemannZeta s := by
    rw [← hsplit]
    exact hΛ
  linear_combination hcomb

/-- **Nonvanishing of the Riemann zeta function times $s - 1$ on $\operatorname{Re} s \ge 1$.**
Let $\zeta$ be the Riemann zeta function and let $\zeta_1 \colon \mathbb{C} \to \mathbb{C}$ be
given by $\zeta_1(s) = (s - 1)\zeta(s)$ for $s \ne 1$ and $\zeta_1(1) = 1$. Then
$\zeta_1(s) \ne 0$ for every complex number $s$ with $\operatorname{Re} s \ge 1$. -/
lemma riemannZeta₁_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta₁ s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hne
  · rw [riemannZeta₁_one]
    exact one_ne_zero
  · have hζ := riemannZeta_ne_zero_of_one_le_re hs
    rw [riemannZeta_eq_inv_sub_mul hne] at hζ
    exact (mul_ne_zero_iff.mp hζ).2

/-- **Meromorphy of the prime logarithmic continuation.** The prime logarithmic continuation $G$
is meromorphic on the open half-plane $\{s \in \mathbb{C} : \operatorname{Re} s > 1/2\}$. -/
theorem logDirichletContinuation_meromorphic :
    MeromorphicOn logDirichletContinuation {s | 1 / 2 < s.re} := by
  have hanal : AnalyticOnNhd ℂ riemannZeta₁ {s : ℂ | 1 / 2 < s.re} :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)
  have hmero := hanal.meromorphicOn
  have hC := logDirichletCorrection_analyticOn.meromorphicOn
  change MeromorphicOn
    (fun s => -(deriv riemannZeta₁ s / riemannZeta₁ s) - logDirichletCorrection s) _
  exact (hmero.deriv.div hmero).neg.sub hC

/-- **Analyticity of the prime logarithmic continuation.** The prime logarithmic continuation
$G$ is analytic at every point of the closed half-plane
$\{s \in \mathbb{C} : \operatorname{Re} s \ge 1\}$. -/
theorem logDirichletContinuation_analyticOn :
    AnalyticOnNhd ℂ logDirichletContinuation {s | 1 ≤ s.re} := by
  have huniv : AnalyticOnNhd ℂ riemannZeta₁ Set.univ :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd isOpen_univ
  have hsub : {s : ℂ | 1 ≤ s.re} ⊆ {s : ℂ | 1 / 2 < s.re} := by
    intro x hx
    change (1 / 2 : ℝ) < x.re
    have hx' : (1 : ℝ) ≤ x.re := hx
    linarith
  have hζ := huniv.mono (s := {s : ℂ | 1 ≤ s.re}) (Set.subset_univ _)
  have hζd := huniv.deriv.mono (s := {s : ℂ | 1 ≤ s.re}) (Set.subset_univ _)
  have hC := logDirichletCorrection_analyticOn.mono hsub
  have hdiv := hζd.div hζ
    (fun x hx => riemannZeta₁_ne_zero_of_one_le_re (show (1 : ℝ) ≤ x.re from hx))
  change AnalyticOnNhd ℂ
    (fun s => -(deriv riemannZeta₁ s / riemannZeta₁ s) - logDirichletCorrection s) _
  exact hdiv.neg.sub hC

/-- **The prime logarithmic continuation on the half-plane $\operatorname{Re} s > 1$.** Let
$\Phi(s) = \sum_p \frac{\log p}{p^s}$ be the prime logarithmic Dirichlet series, summed over all
primes $p$, and let $G$ be the prime logarithmic continuation. Then
$G(s) = \Phi(s) - \frac{1}{s - 1}$ for every complex number $s$ with $\operatorname{Re} s > 1$. -/
theorem logDirichletContinuation_agree :
    Set.EqOn logDirichletContinuation
      (fun s => logDirichletSeries s - 1 / (s - 1)) {s | 1 < s.re} := by
  intro s hs
  have hs' : (1 : ℝ) < s.re := hs
  change -(deriv riemannZeta₁ s / riemannZeta₁ s) - logDirichletCorrection s
    = logDirichletSeries s - 1 / (s - 1)
  have hPhi := logDirichletSeries_eq hs'
  have hne1 : s ≠ 1 := by
    intro h
    rw [h] at hs'
    simp at hs'
  have hζ1 : riemannZeta₁ s ≠ 0 :=
    riemannZeta₁_ne_zero_of_one_le_re (le_of_lt hs')
  have hsub1 : s - 1 ≠ 0 := sub_ne_zero.mpr hne1
  have hinv : (s - 1)⁻¹ ≠ 0 := inv_ne_zero hsub1
  have hid : -deriv riemannZeta s / riemannZeta s
      = 1 / (s - 1) - deriv riemannZeta₁ s / riemannZeta₁ s := by
    rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hne1, riemannZeta_eq_inv_sub_mul hne1]
    field_simp
    ring
  rw [hPhi, hid]
  ring

/-- **Meromorphic continuation of the prime logarithmic Dirichlet series.** Let
$\Phi(s) = \sum_p \frac{\log p}{p^s}$ be the prime logarithmic Dirichlet series. There is a
function $g : \mathbb{C} \to \mathbb{C}$ that is meromorphic on the open half-plane
$\operatorname{Re} s > 1/2$, analytic at every point of the closed half-plane
$\operatorname{Re} s \ge 1$, and satisfies $g(s) = \Phi(s) - \frac{1}{s-1}$ whenever
$\operatorname{Re} s > 1$.

Source: NumberTheoryI Lemma 16.11. -/
theorem logDirichlet_meromorphicContinuation :
    ∃ g : ℂ → ℂ,
      MeromorphicOn g {s | 1 / 2 < s.re} ∧
      AnalyticOnNhd ℂ g {s | 1 ≤ s.re} ∧
      Set.EqOn g (fun s => logDirichletSeries s - 1 / (s - 1))
        {s | 1 < s.re} :=
  ⟨logDirichletContinuation, logDirichletContinuation_meromorphic,
    logDirichletContinuation_analyticOn, logDirichletContinuation_agree⟩

end Nat.Primes
