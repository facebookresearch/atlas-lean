/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import MathlibExt.NumberTheory.ZetaStrideSeriesTendstoStrideAlternatingSumRiemannZeta

import all MathlibExt.NumberTheory.ZetaStrideSeriesTendstoStrideAlternatingSumRiemannZeta
import all MathlibExt.Analysis.SpecialFunctions.Gamma.TwistedDigamma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The half-shift digamma series for alternating stride sums

For positive integers `q` and `t`, the alternating stride sums weighted by
`(2n + q) / ((n + 1/2) (n - 1/2 + q))` have a limit given by two digamma series.
We reindex the finite sums first, then apply dominated convergence to the truncated
alternating rows. Pairing successive terms in each row gives a digamma difference.

## References

* Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta Function and
  Its Associated Functions*, INTEGERS 24 (2024), Article A45, pp. 1–17, Corollary 1, equation (20).
* R. A. Askey and R. Roy, *Gamma Function*, NIST Digital Library of Mathematical Functions,
  §5.7(ii), [equation (5.7.6)](https://dlmf.nist.gov/5.7.E6), for the digamma expansion.
* This proof uses `alternating_bound` from
  `MathlibExt.NumberTheory.ZetaStrideSeriesTendstoStrideAlternatingSumRiemannZeta` and
  `hasSum_digamma_sub_one` from `MathlibExt.Analysis.SpecialFunctions.Gamma.TwistedDigamma`.
-/

namespace MetaMathlibExt

open Filter Finset Topology

private theorem lt_strideCutoff_iff {q n j : ℕ} (hq : 0 < q) :
    j < (n + q - 1) / q ↔ q * j < n := by
  rw [Nat.lt_div_iff_mul_lt hq, Nat.mul_comm j q]
  omega

/-- Reindex the finite triangle by the denominator index `m` rather than `n = m + q*j`. -/
private theorem sum_stride_reindex {q t N : ℕ} (hq : 0 < q) (w : ℕ → ℝ) :
    (∑ n ∈ range N, w n * strideAlternatingSum q t (n + 1)) =
      ∑ m ∈ range N, (1 / ((m : ℝ) + 1) ^ t) *
        ∑ j ∈ range ((N - m + q - 1) / q), (-1 : ℝ) ^ j * w (m + q * j) := by
  classical
  simp only [strideAlternatingSum, mul_sum, sum_sigma']
  refine sum_bij' (fun p _ ↦ ⟨p.1 - q * p.2, p.2⟩) (fun p _ ↦ ⟨p.1 + q * p.2, p.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, j⟩ h
    simp only [mem_sigma, mem_range, lt_strideCutoff_iff hq] at h ⊢
    omega
  · rintro ⟨m, j⟩ h
    simp only [mem_sigma, mem_range, lt_strideCutoff_iff hq] at h ⊢
    omega
  · rintro ⟨n, j⟩ h
    simp only [mem_sigma, mem_range, lt_strideCutoff_iff hq] at h
    dsimp only
    rw [Nat.sub_add_cancel (by omega : q * j ≤ n)]
  · rintro ⟨m, j⟩ _
    simp
  · rintro ⟨n, j⟩ h
    simp only [mem_sigma, mem_range, lt_strideCutoff_iff hq] at h
    dsimp only
    rw [show n + 1 - q * j = n - q * j + 1 by omega,
      Nat.sub_add_cancel (by omega : q * j ≤ n), Nat.cast_add_one]
    ring

private theorem norm_sum_alternating_reciprocal_le {a : ℝ} (ha : 0 < a) (q K : ℕ) :
    ‖∑ j ∈ range K, (-1 : ℝ) ^ j * (1 / (a + q * (j : ℝ)))‖ ≤ 2 * (1 / a) := by
  cases K with
  | zero => simpa only [range_zero, sum_empty, norm_zero] using
      (show 0 ≤ 2 * (1 / a) by positivity)
  | succ k =>
    let f (j : ℕ) : ℝ := 1 / (a + q * (j : ℝ))
    change ‖∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * f j‖ ≤ 2 * (1 / a)
    have hanti : Antitone f := by
      intro i j hij
      dsimp [f]
      gcongr
    calc
      _ = ‖(-1 : ℝ) ^ k * ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * f (k - j)‖ := by
        rw [← sum_range_reflect (fun j ↦ (-1 : ℝ) ^ j * f j) (k + 1), mul_sum]
        congr 1
        refine sum_congr rfl fun j hj ↦ ?_
        have h : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
        rw [show k + 1 - 1 - j = k - j by omega, ← mul_assoc, ← pow_add,
          show k + j = (k - j) + 2 * j by omega, pow_add]
        simp
      _ ≤ 2 * (1 / a) := by
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        simpa [f] using alternating_bound (fun j ↦ f (k - j)) k
          (fun j _ ↦ by dsimp [f]; positivity) (fun j _ ↦ hanti (by omega))

/-- The limit in natural order is identified on the even subsequence. -/
private theorem tendsto_sum_alternating_reciprocal {a : ℝ} (ha : 0 < a) {q : ℕ} (hq : 0 < q) :
    Tendsto (fun K : ℕ ↦ (↑(∑ j ∈ range K, (-1 : ℝ) ^ j * (1 / (a + q * (j : ℝ)))) : ℂ))
      atTop (𝓝 ((Complex.digamma ((↑a + q) / (2 * q)) -
        Complex.digamma (↑a / (2 * q))) / (2 * q))) := by
  let f (j : ℕ) : ℝ := 1 / (a + q * (j : ℝ))
  have hanti : Antitone f := by
    intro i j hij
    dsimp [f]
    gcongr
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hf : Tendsto f atTop (𝓝 0) := by
    have htop := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hqR
    exact (tendsto_atTop_mono (fun _ ↦ le_add_of_nonneg_left ha.le) htop).const_div_atTop 1
  obtain ⟨l, hl⟩ := hanti.tendsto_alternating_series_of_tendsto_zero hf
  have hlC := (Complex.continuous_ofReal.tendsto l).comp hl
  let x : ℂ := ↑a / (2 * q)
  let y : ℂ := (↑a + q) / (2 * q)
  have hx : 0 < x.re := by
    simpa only [x, ← Complex.ofReal_natCast, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      ← Complex.ofReal_div, Complex.ofReal_re] using (show 0 < a / (2 * (q : ℝ)) by positivity)
  have hy : 0 < y.re := by
    simpa only [y, ← Complex.ofReal_natCast, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      ← Complex.ofReal_add, ← Complex.ofReal_div, Complex.ofReal_re] using
      (show 0 < (a + q) / (2 * (q : ℝ)) by positivity)
  have hψ := ((hasSum_digamma_sub_one hy).sub (hasSum_digamma_sub_one hx)).div_const (2 * (q : ℂ))
  have hpair (j : ℕ) : (↑(f (2 * j) - f (2 * j + 1)) : ℂ) =
      ((1 / ((j : ℂ) + 1) - 1 / ((j : ℂ) + y)) -
        (1 / ((j : ℂ) + 1) - 1 / ((j : ℂ) + x))) / (2 * q) := by
    have hxj : (j : ℂ) + x = (↑a + q * (2 * j)) / (2 * q) := by
      dsimp [x]
      field_simp
      ring
    have hyj : (j : ℂ) + y = (↑a + q * (2 * j + 1)) / (2 * q) := by
      dsimp [y]
      field_simp
      ring
    simp only [f, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_ofNat, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one, hxj, hyj, one_div_div]
    have hD : (2 * (q : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) hqC
    simp only [sub_sub_sub_cancel_left, sub_div, div_right_comm (2 * (q : ℂ)) _ (2 * q),
      div_self hD]
  have hblocks (K : ℕ) : ∑ j ∈ range (2 * K), (-1 : ℝ) ^ j * f j =
      ∑ j ∈ range K, (f (2 * j) - f (2 * j + 1)) := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [show 2 * (K + 1) = 2 * K + 1 + 1 by omega,
        sum_range_succ, sum_range_succ, sum_range_succ, ih]
      simp [pow_succ, sub_eq_add_neg, add_assoc]
  have htop : Tendsto (fun K : ℕ ↦ 2 * K) atTop atTop :=
    tendsto_atTop_mono (fun K ↦ by change K ≤ 2 * K; omega) tendsto_id
  have heven : Tendsto (fun K : ℕ ↦ (↑(∑ j ∈ range (2 * K), (-1 : ℝ) ^ j * f j) : ℂ))
      atTop (𝓝 ((Complex.digamma y - Complex.digamma x) / (2 * q))) := by
    simpa only [hblocks, Complex.ofReal_sum, hpair, Function.comp_apply, sub_sub_sub_cancel_right]
      using hψ.tendsto_sum_nat
  have heq := tendsto_nhds_unique (hlC.comp htop) heven
  rwa [← heq]

private theorem tendsto_stride_reciprocal (q t : ℕ) (hq : 0 < q) (ht : 0 < t) (a : ℝ)
    (ha : 0 ≤ a) :
    Tendsto (fun N : ℕ ↦ (↑(∑ n ∈ range N,
      (1 / ((n : ℝ) + 1 + a)) * strideAlternatingSum q t (n + 1)) : ℂ)) atTop
      (𝓝 ((∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ t *
        (Complex.digamma (((n : ℂ) + 1 + ↑a + q) / (2 * q)) -
          Complex.digamma (((n : ℂ) + 1 + ↑a) / (2 * q)))) / (2 * q))) := by
  let w (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1 + a)
  let row (N m : ℕ) : ℝ := (1 / ((m : ℝ) + 1) ^ t) *
    ∑ j ∈ range ((N - m + q - 1) / q), (-1 : ℝ) ^ j * w (m + q * j)
  let g (m : ℕ) : ℂ := (1 / ((m : ℂ) + 1) ^ t) *
    ((Complex.digamma (((m : ℂ) + 1 + ↑a + q) / (2 * q)) -
      Complex.digamma (((m : ℂ) + 1 + ↑a) / (2 * q))) / (2 * q))
  have hw (m j : ℕ) : w (m + q * j) = 1 / (((m : ℝ) + 1 + a) + q * (j : ℝ)) := by
    simp only [w, Nat.cast_add, Nat.cast_mul]
    congr 1
    ring
  have hsum : Summable (fun m : ℕ ↦ 2 * (1 / ((m : ℝ) + 1) ^ (t + 1))) := by
    have hs := Real.summable_one_div_nat_pow.mpr (show 1 < t + 1 by omega)
    simpa only [Nat.cast_add_one] using ((summable_nat_add_iff 1).mpr hs).mul_left 2
  have hlim (m : ℕ) : Tendsto (fun N : ℕ ↦ (↑(row N m) : ℂ)) atTop (𝓝 (g m)) := by
    have htop : Tendsto (fun N : ℕ ↦ (N - m + q - 1) / q) atTop atTop := by
      refine tendsto_atTop.2 fun k ↦ ?_
      filter_upwards [eventually_ge_atTop (m + k * q)] with N hN
      exact (Nat.le_div_iff_mul_le hq).2 (by omega)
    have h := tendsto_sum_alternating_reciprocal (show 0 < (m : ℝ) + 1 + a by positivity) hq
    simpa only [row, hw, g, Function.comp_apply, Complex.ofReal_mul, Complex.ofReal_sum,
      Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_pow] using (h.comp htop).const_mul (1 / ((m : ℂ) + 1) ^ t)
  have hbound (N m : ℕ) : ‖(↑(row N m) : ℂ)‖ ≤ 2 * (1 / ((m : ℝ) + 1) ^ (t + 1)) := by
    rw [Complex.norm_real]
    simp only [row, hw, norm_mul, Real.norm_eq_abs (1 / _), abs_of_nonneg (by positivity :
      0 ≤ 1 / ((m : ℝ) + 1) ^ t)]
    calc
      _ ≤ (1 / ((m : ℝ) + 1) ^ t) * (2 * (1 / ((m : ℝ) + 1 + a))) :=
        mul_le_mul_of_nonneg_left (norm_sum_alternating_reciprocal_le (by positivity) _ _)
          (by positivity)
      _ ≤ (1 / ((m : ℝ) + 1) ^ t) * (2 * (1 / ((m : ℝ) + 1))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le (by positivity) (le_add_of_nonneg_right ha)) (by norm_num))
          (by positivity)
      _ = _ := by rw [mul_left_comm, one_div_mul_one_div, pow_succ]
  have h := tendsto_tsum_of_dominated_convergence hsum hlim (Eventually.of_forall hbound)
  have htsum (N : ℕ) : (∑' m : ℕ, (↑(row N m) : ℂ)) =
      (↑(∑ n ∈ range N, w n * strideAlternatingSum q t (n + 1)) : ℂ) := by
    rw [tsum_eq_sum (s := range N), sum_stride_reindex hq w, Complex.ofReal_sum]
    intro m hm
    have hm' : N ≤ m := Nat.le_of_not_gt (fun h ↦ hm (mem_range.mpr h))
    simp [row, Nat.sub_eq_zero_of_le hm', Nat.div_eq_of_lt (show q - 1 < q by omega)]
  simpa only [htsum, g, ← mul_div_assoc, tsum_div_const, w] using h

/-- **Digamma series for the alternating stride sum.** Let $q \ge 1$ and $t \ge 1$ be integers,
let $S_{q,t}$ denote the alternating stride sum and $\psi$ the digamma function. As
$N \to \infty$, the partial sums
$$
\sum_{n=1}^{N} \frac{2n + q}{(n + \frac12)(n - \frac12 + q)} \, S_{q,t}(n)
$$
converge to
$$
\frac{1}{2q} \sum_{n=1}^{\infty} \frac{1}{n^t}
\left[\psi\left(\frac{n+\frac12+q}{2q}\right) - \psi\left(\frac{n+\frac12}{2q}\right)\right] +
\frac{1}{2q} \sum_{n=1}^{\infty} \frac{1}{n^t}
\left[\psi\left(\frac{n-\frac12+2q}{2q}\right) - \psi\left(\frac{n-\frac12+q}{2q}\right)\right].
$$

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Corollary 1,
equation (20). -/
public theorem tendsto_strideAlternatingSum_digamma_half (q t : ℕ) (hq : 0 < q)
    (ht : 0 < t) :
    Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
        (2 * ((n : ℝ) + 1) + q) / (((n : ℝ) + 1 + 1 / 2) * ((n : ℝ) + 1 - 1 / 2 + q)) *
          strideAlternatingSum q t (n + 1) : ℝ) : ℂ))
      atTop (𝓝 ((∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ t *
          (Complex.digamma (((n : ℂ) + 1 + 1 / 2 + q) / (2 * q)) -
            Complex.digamma (((n : ℂ) + 1 + 1 / 2) / (2 * q)))) / (2 * q) +
        (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ t *
          (Complex.digamma (((n : ℂ) + 1 - 1 / 2 + 2 * q) / (2 * q)) -
            Complex.digamma (((n : ℂ) + 1 - 1 / 2 + q) / (2 * q)))) / (2 * q))) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h := (tendsto_stride_reciprocal q t hq ht (1 / 2) (by norm_num)).add
    (tendsto_stride_reciprocal q t hq ht (q - 1 / 2) (by linarith))
  have h₁ (x : ℂ) : x + ((q : ℂ) - 1 / 2) = x - 1 / 2 + q := by ring
  have h₂ (x : ℂ) : x - 1 / 2 + (q : ℂ) + q = x - 1 / 2 + 2 * q := by ring
  simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.ofReal_natCast, h₁, h₂] at h
  refine h.congr fun N ↦ ?_
  rw [← Complex.ofReal_add, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun n _ ↦ ?_
  have h₃ : 0 < (n : ℝ) + 1 + 1 / 2 := by positivity
  have h₄ : 0 < (n : ℝ) + 1 - 1 / 2 + q := by
    linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  rw [show (n : ℝ) + 1 + (q - 1 / 2) = (n : ℝ) + 1 - 1 / 2 + q by ring,
    ← add_mul, div_add_div 1 1 h₃.ne' h₄.ne']
  congr 2
  ring

end MetaMathlibExt
