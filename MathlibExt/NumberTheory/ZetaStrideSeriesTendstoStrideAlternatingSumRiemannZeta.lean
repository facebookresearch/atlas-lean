/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Alternating stride sum series for the Riemann zeta function

This module defines the alternating stride sum. For integers $q,t \ge 1$, it proves that the
partial sums with weight $1/n + 1/(n+q)$ converge to $\zeta(t+1)$, and that for nonnegative
even integers $p$ the partial sums with weight $1/n^{p+1} + 1/(n+q)^{p+1}$ converge to
$\zeta(p+t+1)$. The proof uses the stride recurrence and finite telescoping; it does not
need the parity hypothesis, which is retained in the statement of Theorem 4.

## References

* Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
  Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, pp. 1–17,
  Theorem 1, equation (9), and Theorem 4, equation (32), first equality.
  The higher-power proof generalizes the finite telescoping proof already used here for
  `tendsto_strideAlternatingSum_riemannZeta`.
-/

namespace MetaMathlibExt

open Filter Topology

@[expose] public section

/-- **Alternating stride sum.** For natural numbers $q$, $t$ and $n$, let
$K = \lfloor (n + q - 1)/q \rfloor$ if $q \ge 1$ and $K = 0$ if $q = 0$. The alternating stride
sum is the real number
$$
S_{q,t}(n) = \sum_{i=0}^{K-1} \frac{(-1)^i}{(n - qi)^t}.
$$
For $q \ge 1$ this is the alternating sum of $m^{-t}$ over $m = n, n - q, n - 2q, \dots$ with
$m \ge 1$; with $j = i + 1$ it reads $\sum_{j=1}^{K} (-1)^{j+1}/(n + q - qj)^t$.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 1,
equation (9). -/
public noncomputable def strideAlternatingSum (q t n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range ((n + q - 1) / q), (-1 : ℝ) ^ i / ((n - q * i : ℕ) : ℝ) ^ t

private theorem div_eq_one_of_le_local {q n : ℕ} (hn : 0 < n) (hnq : n ≤ q) :
    (n + q - 1) / q = 1 :=
  Nat.div_eq_of_lt_le (by omega) (by omega)

private theorem div_add_eq_local {q n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    (n + q + q - 1) / q = (n + q - 1) / q + 1 := by
  rw [(by omega : n + q + q - 1 = n + q - 1 + q), Nat.add_div_right _ hq]

/-- **Alternating stride sum with a single term.** For natural numbers $q$, $t$ and $n$ with
$1 \le n \le q$, the alternating stride sum satisfies $S_{q,t}(n) = 1/n^t$.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, equation (9). -/
public theorem strideAlternatingSum_of_le {q t n : ℕ} (hn : 0 < n) (hnq : n ≤ q) :
    strideAlternatingSum q t n = 1 / (n : ℝ) ^ t := by
  simp [strideAlternatingSum, div_eq_one_of_le_local hn hnq]

/-- **Recurrence for the alternating stride sum.** Let $q \ge 1$, $n \ge 1$ and $t \ge 0$ be
integers and let $S_{q,t}$ denote the alternating stride sum. Then
$S_{q,t}(n + q) = 1/(n + q)^t - S_{q,t}(n)$.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, equation (9). -/
public theorem strideAlternatingSum_add {q t n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    strideAlternatingSum q t (n + q) = 1 / ((n + q : ℕ) : ℝ) ^ t - strideAlternatingSum q t n := by
  rw [strideAlternatingSum, div_add_eq_local hq hn, Finset.sum_range_succ', strideAlternatingSum,
    sub_eq_neg_add, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [(by rw [Nat.mul_succ]; omega : n + q - q * (i + 1) = n - q * i), pow_succ]
    ring

/-- If `a 0, …, a K` are nonnegative and nondecreasing, the norm of their alternating sum
is at most twice the last term `a K`. -/
public theorem norm_sum_range_neg_one_pow_mul_le_two_mul (a : ℕ → ℝ) (K : ℕ)
    (ha : ∀ i ≤ K, 0 ≤ a i) (hm : ∀ i < K, a i ≤ a (i + 1)) :
    ‖∑ i ∈ Finset.range (K + 1), (-1 : ℝ) ^ i * a i‖ ≤ 2 * a K := by
  have hid : (∑ i ∈ Finset.range (K + 1), (-1 : ℝ) ^ i * a i) =
      a K * (∑ i ∈ Finset.range (K + 1), (-1 : ℝ) ^ i) -
        ∑ i ∈ Finset.range K, (a (i + 1) - a i) *
          (∑ j ∈ Finset.range (i + 1), (-1 : ℝ) ^ j) := by
    simpa [smul_eq_mul, mul_comm] using
      Finset.sum_range_by_parts a (fun i => (-1 : ℝ) ^ i) (K + 1)
  rw [hid]
  calc
    _ ≤ ‖a K * (∑ i ∈ Finset.range (K + 1), (-1 : ℝ) ^ i)‖ +
        ‖∑ i ∈ Finset.range K, (a (i + 1) - a i) *
          (∑ j ∈ Finset.range (i + 1), (-1 : ℝ) ^ j)‖ := norm_sub_le _ _
    _ ≤ a K + ∑ i ∈ Finset.range K, (a (i + 1) - a i) := by
      apply add_le_add
      · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (ha K le_rfl)]
        simpa using mul_le_mul_of_nonneg_left (norm_sum_neg_one_pow_le (K + 1)) (ha K le_rfl)
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
        have h := sub_nonneg.mpr (hm i (Finset.mem_range.mp hi))
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg h]
        simpa using mul_le_mul_of_nonneg_left (norm_sum_neg_one_pow_le (i + 1)) h
    _ ≤ 2 * a K := by
      rw [Finset.sum_range_sub]
      linarith [ha 0 (Nat.zero_le K)]

private theorem stride_bound (q t n : ℕ) (hq : 0 < q) (hn : 0 < n) :
    ‖strideAlternatingSum q t n‖ ≤ 2 := by
  have hK : 0 < (n + q - 1) / q := by
    apply Nat.div_pos
    · omega
    · exact hq
  obtain ⟨K, hK⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
  have hpos (i : ℕ) (hi : i ≤ K) : 0 < n - q * i := by
    have hlt : i < (n + q - 1) / q := by omega
    have hmul := (Nat.le_div_iff_mul_le hq).mp (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul, Nat.mul_comm i q] at hmul
    omega
  have ha (i : ℕ) (hi : i ≤ K) : 0 ≤ 1 / ((n - q * i : ℕ) : ℝ) ^ t := by
    positivity
  have hm (i : ℕ) (hi : i < K) :
      1 / ((n - q * i : ℕ) : ℝ) ^ t ≤ 1 / ((n - q * (i + 1) : ℕ) : ℝ) ^ t := by
    apply one_div_le_one_div_of_le
    · exact pow_pos (by exact_mod_cast hpos (i + 1) (by omega)) t
    · apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast Nat.sub_le_sub_left (Nat.mul_le_mul_left q (Nat.le_succ i)) n
  have hb : 1 / ((n - q * K : ℕ) : ℝ) ^ t ≤ 1 := by
    apply (div_le_one (pow_pos (by exact_mod_cast hpos K le_rfl) t)).mpr
    exact one_le_pow₀ (by exact_mod_cast hpos K le_rfl)
  calc
    ‖strideAlternatingSum q t n‖ =
        ‖∑ i ∈ Finset.range (K + 1), (-1 : ℝ) ^ i *
          (1 / ((n - q * i : ℕ) : ℝ) ^ t)‖ := by
      simp [strideAlternatingSum, hK, div_eq_mul_inv]
    _ ≤ 2 * (1 / ((n - q * K : ℕ) : ℝ) ^ t) :=
      norm_sum_range_neg_one_pow_mul_le_two_mul _ K ha hm
    _ ≤ 2 := by linarith

private theorem weighted_term (q t p n : ℕ) (hq : 0 < q) (hn : 0 < n) :
    ((n : ℝ) ^ (p + 1) + ((n : ℝ) + q) ^ (p + 1)) /
        ((n : ℝ) * ((n : ℝ) + q)) ^ (p + 1) * strideAlternatingSum q t n =
      strideAlternatingSum q t n / (n : ℝ) ^ (p + 1) -
        strideAlternatingSum q t (n + q) / ((n + q : ℕ) : ℝ) ^ (p + 1) +
          1 / ((n + q : ℕ) : ℝ) ^ (p + t + 1) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnq' : 0 < ((n + q : ℕ) : ℝ) := by exact_mod_cast (show 0 < n + q by omega)
  have hweight :
      ((n : ℝ) ^ (p + 1) + ((n + q : ℕ) : ℝ) ^ (p + 1)) /
          ((n : ℝ) * ((n + q : ℕ) : ℝ)) ^ (p + 1) =
        1 / (n : ℝ) ^ (p + 1) + 1 / ((n + q : ℕ) : ℝ) ^ (p + 1) := by
    rw [div_add_div 1 1 (pow_ne_zero _ hn'.ne') (pow_ne_zero _ hnq'.ne'), mul_pow]
    ring
  rw [← Nat.cast_add, hweight, strideAlternatingSum_add hq hn,
    show p + t + 1 = t + (p + 1) by omega, pow_add ((n + q : ℕ) : ℝ) t (p + 1)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem finite_identity (q t p : ℕ) (hq : 0 < q) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (((n : ℝ) + 1) ^ (p + 1) + ((n : ℝ) + 1 + q) ^ (p + 1)) /
        (((n : ℝ) + 1) * ((n : ℝ) + 1 + q)) ^ (p + 1) * strideAlternatingSum q t (n + 1)) =
      (∑ n ∈ Finset.range (N + q), 1 / ((n + 1 : ℕ) : ℝ) ^ (p + t + 1)) -
        ∑ j ∈ Finset.range q,
          strideAlternatingSum q t (N + j + 1) / ((N + j + 1 : ℕ) : ℝ) ^ (p + 1) := by
  let f (n : ℕ) := strideAlternatingSum q t (n + 1) / ((n + 1 : ℕ) : ℝ) ^ (p + 1)
  let g (n : ℕ) := 1 / ((n + 1 : ℕ) : ℝ) ^ (p + t + 1)
  have h₀ : ∑ n ∈ Finset.range q, f n = ∑ n ∈ Finset.range q, g n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    dsimp [f, g]
    rw [strideAlternatingSum_of_le (Nat.succ_pos n) (Finset.mem_range.mp hn), div_div,
      ← pow_add, show t + (p + 1) = p + t + 1 by omega]
  calc
    _ = ∑ n ∈ Finset.range N, (f n - f (q + n) + g (q + n)) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      simpa only [f, g, Nat.cast_add, Nat.cast_one, Nat.add_right_comm, Nat.add_comm q] using
        weighted_term q t p (n + 1) hq (Nat.succ_pos n)
    _ = (∑ n ∈ Finset.range (N + q), g n) - ∑ j ∈ Finset.range q, f (N + j) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have hf := (Finset.sum_range_add f N q).symm.trans
        (by simpa only [Nat.add_comm q N] using Finset.sum_range_add f q N)
      have hg := Finset.sum_range_add g q N
      rw [Nat.add_comm q N] at hg
      linarith

private theorem stride_div_tendsto_zero (q t p j : ℕ) (hq : 0 < q) :
    Tendsto (fun N : ℕ => strideAlternatingSum q t (N + j + 1) /
      ((N + j + 1 : ℕ) : ℝ) ^ (p + 1)) atTop (𝓝 (0 : ℝ)) := by
  apply squeeze_zero_norm (a := fun N : ℕ => 2 / (N + j + 1 : ℕ))
  · intro N
    have hn : 1 ≤ ((N + j + 1 : ℕ) : ℝ) := Nat.one_le_cast.mpr (by omega)
    rw [norm_div, norm_pow, Real.norm_natCast]
    calc
      _ ≤ 2 / ((N + j + 1 : ℕ) : ℝ) ^ (p + 1) :=
        div_le_div_of_nonneg_right (stride_bound q t (N + j + 1) hq (by omega)) (by positivity)
      _ ≤ 2 / (N + j + 1 : ℕ) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        simpa only [pow_one] using pow_le_pow_right₀ hn (show 1 ≤ p + 1 by omega)
  · exact (tendsto_natCast_atTop_atTop (R := ℝ) |>.comp
      (tendsto_add_atTop_nat (j + 1))).const_div_atTop 2

private theorem boundary_tendsto_zero (q t p : ℕ) (hq : 0 < q) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.range q,
      strideAlternatingSum q t (N + j + 1) / ((N + j + 1 : ℕ) : ℝ) ^ (p + 1))
      atTop (𝓝 (0 : ℝ)) := by
  simpa using tendsto_finsetSum (Finset.range q)
    (fun j _ => stride_div_tendsto_zero q t p j hq)

private theorem zeta_partial_sums (t : ℕ) (ht : 0 < t) :
    Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
      1 / ((n + 1 : ℕ) : ℝ) ^ (t + 1) : ℝ) : ℂ))
      atTop (𝓝 (riemannZeta ((t : ℂ) + 1))) := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (t + 1)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have hsc : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (t + 1)) := by
    simpa using Complex.summable_ofReal.mpr hs
  have hz : riemannZeta ((t : ℂ) + 1) =
      ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℂ) ^ (t + 1) := by
    rw [← Nat.cast_add_one, zeta_nat_eq_tsum_of_gt_one (by omega), hsc.tsum_eq_zero_add]
    simp [zero_pow (by omega : t + 1 ≠ 0)]
  have hshift := (summable_nat_add_iff 1).mpr hsc
  rw [hz]
  simpa using hshift.hasSum.tendsto_sum_nat

private theorem tendsto_strideAlternatingSum_riemannZeta_pow (q t p : ℕ) (hq : 0 < q)
    (ht : 0 < t) :
    Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
        (((n : ℝ) + 1) ^ (p + 1) + ((n : ℝ) + 1 + q) ^ (p + 1)) /
          (((n : ℝ) + 1) * ((n : ℝ) + 1 + q)) ^ (p + 1) *
            strideAlternatingSum q t (n + 1) : ℝ) : ℂ))
      atTop (𝓝 (riemannZeta ((p : ℂ) + t + 1))) := by
  have hz := (zeta_partial_sums (p + t) (by omega)).comp (tendsto_add_atTop_nat q)
  have hb := (Complex.continuous_ofReal.tendsto 0).comp (boundary_tendsto_zero q t p hq)
  have h := hz.sub hb
  simp only [Complex.ofReal_zero, sub_zero, Nat.cast_add] at h
  apply h.congr
  intro N
  simp only [Function.comp_apply, finite_identity q t p hq N, Complex.ofReal_sub, Nat.cast_add]

/-- **Alternating stride sum series for $\zeta(t + 1)$.** Let $q \ge 1$ and $t \ge 1$ be integers
and let $S_{q,t}$ denote the alternating stride sum. Then the partial sums
$$
\sum_{n=1}^{N} \frac{2n + q}{n(n + q)} \, S_{q,t}(n)
$$
converge to $\zeta(t + 1)$ as $N \to \infty$, where $\zeta$ is the Riemann zeta function.

The series converges only conditionally, which is why it is stated through its partial sums.
On the subsequence $n = 1 + mq$, reversing the alternating sum gives a magnitude
$|S_{q,t}(n)| \ge 1 - (1 + q)^{-t}$; the weight is at least $1/n$, yielding a divergent harmonic
lower bound for the series of absolute values. The second expression in equation (9) and the
general identity (8) use a quantity $A^{(t)}$ that the record does not define and are not stated
here.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 1,
equation (9). -/
public theorem tendsto_strideAlternatingSum_riemannZeta (q t : ℕ) (hq : 0 < q)
    (ht : 0 < t) :
    Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
        (2 * ((n : ℝ) + 1) + q) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + q)) *
          strideAlternatingSum q t (n + 1) : ℝ) : ℂ))
      atTop (𝓝 (riemannZeta ((t : ℂ) + 1))) := by
  simpa [pow_one, two_mul, add_assoc] using tendsto_strideAlternatingSum_riemannZeta_pow q t 0 hq ht

/-- **Alternating stride sum series for $\zeta(p + t + 1)$.** Let $q \ge 1$ and $t \ge 1$ be
integers, let $p \ge 0$ be an even integer and let $S_{q,t}$ denote the alternating stride sum.
Then the partial sums
$$
\sum_{n=1}^{N} \frac{n^{p+1} + (n + q)^{p+1}}{(n(n + q))^{p+1}} \, S_{q,t}(n)
$$
converge to $\zeta(p + t + 1)$ as $N \to \infty$, where $\zeta$ is the Riemann zeta function.

This theorem formalizes only the first equality of equation (32).

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 4,
equation (32). -/
public theorem tendsto_strideAlternatingSum_riemannZeta_add (q t p : ℕ) (hq : 0 < q)
    (ht : 0 < t) (hp : Even p) :
    Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
        (((n : ℝ) + 1) ^ (p + 1) + ((n : ℝ) + 1 + q) ^ (p + 1)) /
          (((n : ℝ) + 1) * ((n : ℝ) + 1 + q)) ^ (p + 1) *
            strideAlternatingSum q t (n + 1) : ℝ) : ℂ))
      atTop (𝓝 (riemannZeta ((p : ℂ) + t + 1))) := by
  -- Finite telescoping works without parity; keep the hypothesis of Theorem 4.
  obtain ⟨k, rfl⟩ := hp
  exact tendsto_strideAlternatingSum_riemannZeta_pow q t (k + k) hq ht

end

end MetaMathlibExt
