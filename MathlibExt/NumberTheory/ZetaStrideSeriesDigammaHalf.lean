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
import all MathlibExt.Analysis.Ramanujan.Part1Ch8Entry8Digammaseries
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The half-shift digamma series for alternating stride sums

For positive integers `q` and `t`, the alternating stride sums weighted by
`(2n + q) / ((n + 1/2) (n - 1/2 + q))` have a limit given by two digamma series.
We reindex the finite sums first, then apply dominated convergence to the truncated
alternating rows. Ramanujan's alternating digamma series gives the limit of each row.

## References

* Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta Function and
  Its Associated Functions*, INTEGERS 24 (2024), Article A45, pp. 1–17, Corollary 1, equation (20).
* Bruce C. Berndt, *Ramanujan's Notebooks, Part I* (Springer-Verlag, 1985), Chapter 8, Entry 8.
  We use `ramanujan_part1_ch8_entry8_digammaseries_complex_digamma` and `bridge_iff` from
  `MathlibExt.Analysis.Ramanujan.Part1Ch8Entry8Digammaseries`.
* The finite row bound uses `alternating_bound` from
  `MathlibExt.NumberTheory.ZetaStrideSeriesTendstoStrideAlternatingSumRiemannZeta`.
-/

namespace MetaMathlibExt

open Filter Finset Topology

private theorem lt_strideCutoff_iff {q n j : ℕ} (hq : 0 < q) :
    j < (n + q - 1) / q ↔ q * j < n := by
  rw [← Nat.ceilDiv_eq_add_pred_div]
  simpa only [not_le] using (ceilDiv_le_iff_le_mul (b := n) (c := j) hq).not

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

open MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries in
/-- Ramanujan's Entry 8 with parameters `a - q` and `q`. -/
private theorem tendsto_sum_alternating_reciprocal {a : ℝ} (ha : 0 < a) {q : ℕ} (hq : 0 < q) :
    Tendsto (fun K : ℕ ↦ (↑(∑ j ∈ range K, (-1 : ℝ) ^ j * (1 / (a + q * (j : ℝ)))) : ℂ))
      atTop (𝓝 ((Complex.digamma ((↑a + q) / (2 * q)) -
        Complex.digamma (↑a / (2 * q))) / (2 * q))) := by
  have hq₀ : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hden (j : ℕ) : (a : ℂ) - q + q * ((j + 1 : ℕ) : ℂ) = a + q * (j : ℂ) := by
    push_cast
    ring
  have hne (j : ℕ) : (a : ℂ) - q + q * ((j + 1 : ℕ) : ℂ) ≠ 0 := by
    rw [hden]
    exact_mod_cast (show a + (q : ℝ) * (j : ℝ) ≠ 0 by positivity)
  have h := (bridge_iff _ _).mp
    (ramanujan_part1_ch8_entry8_digammaseries_complex_digamma ((a : ℂ) - q) q hq₀ hne)
  rw [show (a : ℂ) - q + 2 * q = a + q by ring, sub_add_cancel] at h
  simpa only [chapter8Entry8Term, hden, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_natCast, mul_one_div] using h

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
