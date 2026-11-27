/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.RingTheory.RootsOfUnity.Complex
import MathlibExt.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# A twisted sum of digamma values

The finite Fourier transform of the digamma values at the fractions of denominator `p`
is given at each nonzero frequency by a principal logarithm.
-/

open Complex Filter Finset Topology

namespace MetaMathlibExt

/-- Shift the digamma series from the half-plane `1 < re s` to `0 < re s`
using the recurrence at both `s` and the reference point `1`. -/
private theorem hasSum_digamma_sub_one {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun j : ℕ ↦ 1 / ((j : ℂ) + 1) - 1 / ((j : ℂ) + s))
      (digamma s - digamma 1) := by
  rw [← hasSum_nat_add_iff' 1]
  have h := (Complex.hasSum_digamma_series (s + 1) (by simpa using hs)).sub
    (Complex.hasSum_digamma_series (1 + 1) (by norm_num))
  have shift (u : ℂ) (hu : 0 < u.re) := digamma_apply_add_one u fun m he ↦
    (Nat.cast_nonneg m : 0 ≤ (m : ℝ)).not_gt (by simpa [he] using hu)
  rw [shift s hs, shift 1 (by norm_num)] at h
  convert h using 1
  · ext n
    simp only [Nat.cast_add_one, digammaSeriesTerm]
    ring_nf
  · simp
    ring

/-- The ordered logarithm series at a point of the unit circle distinct from one. -/
private theorem tendsto_log_series {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1) :
    Tendsto (fun N ↦ ∑ n ∈ range N, z ^ (n + 1) / (n + 1 : ℂ))
      atTop (𝓝 (-log (1 - z))) := by
  have hanti : Antitone (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) := by
    intro i j hij
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hij)
  have hb (n : ℕ) : ‖∑ i ∈ range n, z ^ (i + 1)‖ ≤ 2 / ‖z - 1‖ := by
    simp_rw [pow_succ, ← sum_mul, norm_mul, hz, mul_one, geom_sum_eq hne, norm_div]
    gcongr
    simpa [norm_pow, hz, one_add_one_eq_two] using norm_sub_le (z ^ n) 1
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete
    (hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded
      tendsto_one_div_add_atTop_nhds_zero_nat hb)
  have hshift : Tendsto (fun N ↦ ∑ n ∈ range N, z ^ (n + 1) / (n + 1 : ℂ)) atTop (𝓝 l) := by
    simpa [real_smul, div_eq_inv_mul] using hl
  have hfull : Tendsto (fun N ↦ ∑ n ∈ range N, z ^ n / n) atTop (𝓝 l) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    simpa [sum_range_succ'] using hshift
  have habel := tendsto_map'_iff.mp (Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hfull)
  have hlog : Tendsto (fun r : ℝ ↦ -log (1 - z * r)) (𝓝[<] 1) (𝓝 l) := by
    apply habel.congr'
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with r hr
    have hrz : ‖z * r‖ < 1 := by simpa [norm_mul, hz, abs_of_nonneg hr.1.le] using hr.2
    simpa [Function.comp_apply, mul_pow, div_mul_eq_mul_div] using
      (hasSum_taylorSeries_neg_log hrz).tsum_eq
  have hslit : 1 - z ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr ∘ Or.inl
    simp only [sub_re, one_re]
    nlinarith [norm_sub_one_sq_eq_of_norm_eq_one hz,
      sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))]
  have hcont : ContinuousAt (fun r : ℝ ↦ -log (1 - z * r)) 1 := by
    apply ContinuousAt.neg
    apply ContinuousAt.clog (by fun_prop)
    simpa using hslit
  have heq := tendsto_nhds_unique hlog hcont.continuousWithinAt
  rwa [show l = -log (1 - z) by simpa using heq] at hshift

/-- For a nontrivial root, summing the digamma series over a period cancels its
harmonic reference terms and gives a block of the logarithm series. -/
private theorem sum_pow_mul_digamma {z : ℂ} {p : ℕ} (hp : 0 < p)
    (hpow : z ^ p = 1) (hne : z ≠ 1) :
    ∑ a ∈ range p, z ^ (a + 1) * digamma ((a + 1 : ℂ) / p) = p * log (1 - z) := by
  let x (a : ℕ) : ℂ := (a + 1 : ℂ) / p
  let f (n : ℕ) : ℂ := z ^ (n + 1) / (n + 1 : ℂ)
  have hcancel : ∑ a ∈ range p, z ^ (a + 1) = 0 := by
    simp [pow_succ, ← sum_mul, geom_sum_eq hne, hpow]
  have hseries (a : ℕ) : HasSum
      (fun j : ℕ ↦ z ^ (a + 1) * (1 / ((j : ℂ) + 1) - 1 / ((j : ℂ) + x a)))
      (z ^ (a + 1) * (digamma (x a) - digamma 1)) := by
    apply HasSum.mul_left
    apply hasSum_digamma_sub_one
    change 0 < (((a : ℂ) + 1) / ((p : ℝ) : ℂ)).re
    rw [div_ofReal_re]
    simp only [add_re, natCast_re, one_re]
    positivity
  have hsum := (hasSum_sum (s := range p) fun a _ ↦ hseries a).tendsto_sum_nat
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, hcancel, zero_mul, zero_sub, sub_zero] at hsum
  have hblock (j : ℕ) : (∑ a ∈ range p, z ^ (a + 1) * (1 / ((j : ℂ) + x a))) =
      p * ∑ a ∈ range p, f (j * p + a) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro a _
    have hd : (j : ℂ) + x a = (j * (p : ℂ) + a + 1) / p := by
      dsimp [x]
      field_simp [Nat.cast_ne_zero.mpr hp.ne']
      ring
    have hzj : z ^ (j * p + a + 1) = z ^ (a + 1) := by
      rw [Nat.add_assoc, pow_add, Nat.mul_comm j, pow_mul, hpow, one_pow, one_mul]
    simp only [hd, one_div_div, f, hzj, Nat.cast_add, Nat.cast_mul]
    ring
  have hblocks (N : ℕ) :
      ∑ j ∈ range N, ∑ a ∈ range p, f (j * p + a) = ∑ n ∈ range (N * p), f n := by
    induction N with
    | zero => simp
    | succ N ih => rw [sum_range_succ, Nat.succ_mul, sum_range_add, ih]
  simp_rw [hblock, sum_neg_distrib, ← mul_sum, hblocks] at hsum
  have htop : Tendsto (fun N : ℕ ↦ N * p) atTop atTop :=
    tendsto_atTop_mono (fun N ↦ Nat.le_mul_of_pos_right N hp) tendsto_id
  have hlog := ((tendsto_log_series (norm_eq_one_of_pow_eq_one hpow hp.ne') hne).comp
    htop).const_mul (p : ℂ)
  simpa [f] using tendsto_nhds_unique hsum hlog.neg

/-- **A twisted sum of digamma values.** Let $p$ and $k$ be natural numbers with $1 \le k < p$,
and let $\psi = \Gamma'/\Gamma$ be the digamma function. Then
$$
\sum_{\alpha=1}^{p} e^{2\pi i k \alpha / p} \, \psi\left( \frac{\alpha}{p} \right) =
p \operatorname{Log}\left( 1 - e^{2\pi i k / p} \right),
$$
where $\operatorname{Log}$ is the principal branch of the complex logarithm.

Source: Jashan Bal, Fern Haraldson, Joshua Males and Ian Thompson, *Jensen Polynomials Associated
with Wright's Circle Method: Hyperbolicity and Turán Inequalities*, INTEGERS 25 (2025),
Article A36, Lemma 3 (`integers-2025-A36-lem-3`). -/
public theorem sum_exp_mul_digamma_div_eq_mul_log_one_sub {p k : ℕ} (hk : 1 ≤ k)
    (hkp : k < p) :
    ∑ α ∈ Finset.Icc 1 p,
        Complex.exp (2 * Real.pi * Complex.I * k * α / p) * Complex.digamma (α / p) =
      p * Complex.log (1 - Complex.exp (2 * Real.pi * Complex.I * k / p)) := by
  have hp : 0 < p := by omega
  let ζ := exp (2 * Real.pi * I / p)
  have hprim := isPrimitiveRoot_exp p hp.ne'
  have hexp (a : ℕ) : exp (2 * Real.pi * I * k * a / p) = (ζ ^ k) ^ a := by
    simp only [ζ, ← exp_nat_mul]
    congr 1
    ring
  have hexp₁ : exp (2 * Real.pi * I * k / p) = ζ ^ k := by simpa using hexp 1
  have hpow : (ζ ^ k) ^ p = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
  simp_rw [hexp]
  rw [hexp₁, ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simpa only [Nat.add_comm 1, Nat.cast_add_one] using
    sum_pow_mul_digamma hp hpow (hprim.pow_ne_one_of_pos_of_lt (by omega) hkp)

end MetaMathlibExt
