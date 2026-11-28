/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecificLimits.Normed

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Signed stride series for the Dirichlet eta function

For positive integers $q$ and $t$, the signed stride sum weighted by
$(-1)^{n+1}(1/n + 1/(n+q))$ gives a series for $\eta(t+1)$. Multiplying the stride recurrence
by the outer sign gives a telescoping difference. The boundary terms vanish because the
signed stride sums are bounded by harmonic numbers.

## References

* Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
  Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, pp. 1–17,
  Theorem 2, equation (25).
* The finite telescoping argument uses the same idea as
  `MetaMathlibExt.tendsto_strideAlternatingSum_riemannZeta` in
  `MathlibExt.NumberTheory.ZetaStrideSeriesTendstoStrideAlternatingSumRiemannZeta`.
-/

namespace MetaMathlibExt

open Filter Topology

@[expose] public section

/-- **Signed stride sum.** For natural numbers $q$, $t$ and $n$, let
$K = \lfloor (n + q - 1)/q \rfloor$ if $q \ge 1$ and $K = 0$ if $q = 0$. The signed stride sum is
the real number
$$
T_{q,t}(n) = \sum_{i=0}^{K-1} \frac{(-1)^{(q+1)i}}{(n - qi)^t}.
$$
With $j = i + 1$ it reads $\sum_{j=1}^{K} (-1)^{(q+1)(j+1)}/(n + q - qj)^t$. For odd $q$ every
sign is $+$, and for even $q$ the signs alternate.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 2,
equation (25). -/
public noncomputable def strideSignedSum (q t n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range ((n + q - 1) / q), (-1 : ℝ) ^ ((q + 1) * i) / ((n - q * i : ℕ) : ℝ) ^ t

private theorem div_eq_one_of_le {q n : ℕ} (hn : 0 < n) (hnq : n ≤ q) :
    (n + q - 1) / q = 1 :=
  Nat.div_eq_of_lt_le (by omega) (by omega)

private theorem div_add_eq {q n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    (n + q + q - 1) / q = (n + q - 1) / q + 1 := by
  rw [show n + q + q - 1 = n + q - 1 + q by omega, Nat.add_div_right _ hq]

/-- **Signed stride sum with a single term.** For natural numbers $q$, $t$ and $n$ with
$1 \le n \le q$, the signed stride sum satisfies $T_{q,t}(n) = 1/n^t$.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, equation (25). -/
public theorem strideSignedSum_of_le {q t n : ℕ} (hn : 0 < n) (hnq : n ≤ q) :
    strideSignedSum q t n = 1 / (n : ℝ) ^ t := by
  simp [strideSignedSum, div_eq_one_of_le hn hnq]

/-- **Recurrence for the signed stride sum.** Let $q \ge 1$, $n \ge 1$ and $t \ge 0$ be integers
and let $T_{q,t}$ denote the signed stride sum. Then
$T_{q,t}(n + q) = 1/(n + q)^t + (-1)^{q+1} T_{q,t}(n)$.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, equation (25). -/
public theorem strideSignedSum_add {q t n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    strideSignedSum q t (n + q) =
      1 / ((n + q : ℕ) : ℝ) ^ t + (-1 : ℝ) ^ (q + 1) * strideSignedSum q t n := by
  rw [strideSignedSum, div_add_eq hq hn, Finset.sum_range_succ', strideSignedSum,
    Finset.mul_sum, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show n + q - q * (i + 1) = n - q * i by rw [Nat.mul_succ]; omega, mul_add, mul_one,
      pow_add]
    ring

-- The harmonic bound works also for odd strides, where the internal signs are all positive.
private theorem norm_strideSignedSum_le_harmonic {q t : ℕ} (hq : 0 < q) (ht : 0 < t)
    (n : ℕ) : ‖strideSignedSum q t (n + 1)‖ ≤ (harmonic (n + 1) : ℝ) := by
  have hterm (m : ℕ) : 1 / ((m + 1 : ℕ) : ℝ) ^ t ≤ ((m + 1 : ℕ) : ℝ)⁻¹ := by
    rw [← one_div]
    refine div_le_div_of_nonneg_left zero_le_one (by positivity) ?_
    simpa only [pow_one] using pow_le_pow_right₀ (Nat.one_le_cast.mpr (Nat.succ_pos m)) ht
  have hmono : Monotone harmonic := monotone_nat_of_le_succ fun k => by
    rw [harmonic_succ]
    exact le_add_of_nonneg_right (by positivity)
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
    by_cases hnq : n + 1 ≤ q
    · rw [strideSignedSum_of_le (Nat.succ_pos n) hnq, Real.norm_of_nonneg (by positivity)]
      have hn : 0 ≤ harmonic n := by simpa only [harmonic_zero] using hmono (Nat.zero_le n)
      exact (hterm n).trans (le_add_of_nonneg_left (by exact_mod_cast hn))
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m + q := ⟨n - q, by omega⟩
      have hn : m + 1 + q = n + 1 := by omega
      have hs := strideSignedSum_add (t := t) hq (Nat.succ_pos m)
      rw [hn] at hs
      rw [hs]
      calc
        _ ≤ ‖(1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ t‖ +
            ‖(-1 : ℝ) ^ (q + 1) * strideSignedSum q t (m + 1)‖ := norm_add_le _ _
        _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ + (harmonic n : ℝ) := by
          rw [Real.norm_of_nonneg (by positivity), norm_mul, norm_pow, norm_neg, norm_one,
            one_pow, one_mul]
          exact add_le_add (hterm n) ((ih m (by omega)).trans (by
            exact_mod_cast hmono (show m + 1 ≤ n by omega)))
        _ = _ := add_comm ..

/-- **Stride series for the Dirichlet eta function.** Let $q, t \ge 1$ be integers and let
$T_{q,t}(n)$ denote the signed stride sum. Then the partial sums
$$\sum_{n=1}^{N} (-1)^{n+1} \frac{2n+q}{n(n+q)} T_{q,t}(n)$$
converge, as $N \to \infty$, to $\eta(t+1)$, where $\eta(s) = \sum_{n \ge 1} (-1)^{n+1} n^{-s}$ is
the Dirichlet eta function.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 2,
equation (25). -/
public theorem tendsto_strideSignedSum_dirichletEta (q t : ℕ) (hq : 0 < q)
    (ht : 0 < t) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ n * (2 * ((n : ℝ) + 1) + q) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + q)) *
          strideSignedSum q t (n + 1))
      atTop (𝓝 (∑' n : ℕ, (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ (t + 1))) := by
  let s (n : ℕ) := (-1 : ℝ) ^ n * strideSignedSum q t (n + 1)
  let f (n : ℕ) := s n / ((n : ℝ) + 1)
  let g (n : ℕ) := (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ (t + 1)
  let w (n : ℕ) :=
    (-1 : ℝ) ^ n * (2 * ((n : ℝ) + 1) + q) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + q)) *
      strideSignedSum q t (n + 1)
  have hsign : (-1 : ℝ) ^ q * (-1) ^ (q + 1) = -1 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]
    norm_num
  have hstep (n : ℕ) :
      s (n + q) = (-1 : ℝ) ^ (n + q) / (((n + q : ℕ) : ℝ) + 1) ^ t - s n := by
    have h := strideSignedSum_add (t := t) hq (Nat.succ_pos n)
    rw [Nat.add_right_comm n 1 q] at h
    dsimp only [s]
    rw [h, mul_add, pow_add (-1 : ℝ) n q,
      ← mul_assoc ((-1 : ℝ) ^ n * (-1) ^ q),
      mul_assoc ((-1 : ℝ) ^ n) ((-1) ^ q) ((-1) ^ (q + 1)), hsign]
    push_cast
    ring
  have hterm (n : ℕ) : w n + f (n + q) = f n + g (n + q) := by
    have hweight :
        (2 * ((n : ℝ) + 1) + q) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + q)) =
          1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1 + q) := by
      rw [div_add_div _ _ (by positivity) (by positivity)]
      ring
    have hw : w n = (1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1 + q)) * s n := by
      dsimp only [w, s]
      rw [← hweight]
      ring
    rw [hw]
    dsimp only [f, g]
    rw [hstep, show (((n + q : ℕ) : ℝ) + 1) = (n : ℝ) + 1 + q by push_cast; ring,
      pow_succ _ t]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hinit : ∑ n ∈ Finset.range q, f n = ∑ n ∈ Finset.range q, g n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    dsimp only [f, g, s]
    rw [strideSignedSum_of_le (Nat.succ_pos n) (Finset.mem_range.mp hn), Nat.cast_succ,
      pow_succ _ t]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hfin (N : ℕ) :
      (∑ n ∈ Finset.range N, w n) =
        (∑ n ∈ Finset.range (N + q), g n) - ∑ j ∈ Finset.range q, f (N + j) := by
    have hfN := Finset.sum_range_add f N q
    have hfq := Finset.sum_range_add f q N
    have hgq := Finset.sum_range_add g q N
    rw [Nat.add_comm q N] at hfq hgq
    have h := Finset.sum_congr (s₁ := Finset.range N) rfl (fun n _ => hterm n)
    simp only [Finset.sum_add_distrib, Nat.add_comm _ q] at h
    linarith
  have hf : Tendsto f atTop (𝓝 0) := by
    have hlog : Tendsto (fun x : ℝ => (1 + Real.log x) / x) atTop (𝓝 0) := by
      have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
        simpa only [pow_one, one_mul, add_zero] using
          Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      simpa only [add_div, id_eq, zero_add] using
        (show Tendsto (id : ℝ → ℝ) atTop atTop from tendsto_id).const_div_atTop 1 |>.add h
    apply squeeze_zero_norm (a := fun n : ℕ => (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1))
    · intro n
      dsimp only [f, s]
      rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Real.norm_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      refine (norm_strideSignedSum_le_harmonic hq ht n).trans ?_
      simpa only [Nat.cast_add, Nat.cast_one] using harmonic_le_one_add_log (n + 1)
    · simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        hlog.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  have hboundary : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range q, f (N + j)) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range q) (fun j _ => hf.comp (tendsto_add_atTop_nat j))
  have hgAbs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (t + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (show 1 < t + 1 by omega))
  have hg : Summable g := hgAbs.of_norm_bounded fun n => by
    dsimp only [g]
    rw [norm_div, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
      Real.norm_of_nonneg (by positivity)]
  have hlim := (hg.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat q)).sub hboundary
  simp only [sub_zero] at hlim
  exact hlim.congr fun N => (hfin N).symm

end

end MetaMathlibExt
