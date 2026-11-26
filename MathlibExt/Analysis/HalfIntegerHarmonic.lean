/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Harmonic numbers of half-integer index

The digamma value at one half and the iterated recurrence give the first-order value.
Splitting the Riemann zeta series into even and odd terms gives the second- and third-order values.
A finite telescoping identity handles differences of half-integer tails at every order.
-/

namespace MetaMathlibExt

open Filter Finset
open scoped Topology

-- The two finite sums over `range (N + k)` differ only in how the terms are grouped.
private lemma sum_range_sub_shift {α : Type*} [AddCommGroup α] (f : ℕ → α) (k N : ℕ) :
    ∑ j ∈ range N, (f j - f (j + k)) =
      (∑ j ∈ range k, f j) - ∑ j ∈ range k, f (N + j) := by
  have h₁ := sum_range_add f N k
  have h₂ := sum_range_add f k N
  rw [Nat.add_comm k N] at h₂
  rw [sum_sub_distrib]
  simp only [Nat.add_comm k] at h₂
  exact sub_eq_sub_iff_add_eq_add.mpr (h₁.symm.trans h₂)

private lemma hasSum_half_pow_sub_shift (k m : ℕ) :
    HasSum (fun j : ℕ ↦ 1 / ((j : ℂ) + 1 / 2) ^ (m + 1) -
        1 / ((j : ℂ) + k + 1 / 2) ^ (m + 1))
      (∑ j ∈ range k, 1 / ((j : ℂ) + 1 / 2) ^ (m + 1)) := by
  let f (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1 / 2) ^ (m + 1)
  have h₀ : Tendsto f atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1 / 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa [f, one_div, inv_pow, zero_pow (Nat.succ_ne_zero m)] using
      (tendsto_inv_atTop_zero.comp h).pow (m + 1)
  have hnonneg (n : ℕ) : 0 ≤ f n - f (n + k) := by
    apply sub_nonneg.mpr
    dsimp only [f]
    apply one_div_le_one_div_of_le (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    exact add_le_add (Nat.cast_le.mpr (Nat.le_add_right n k)) le_rfl
  have h : HasSum (fun j ↦ f j - f (j + k)) (∑ j ∈ range k, f j) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).2
    have ht (j : ℕ) : Tendsto (fun N ↦ f (N + j)) atTop (𝓝 0) :=
      h₀.comp (tendsto_add_atTop_nat j)
    simpa only [sum_range_sub_shift, sum_const_zero, sub_zero] using
      tendsto_const_nhds.sub (tendsto_finsetSum (range k) (fun j _ ↦ ht j))
  simpa [f, Nat.cast_add] using Complex.hasSum_ofReal.mpr h

private lemma half_inv_pow (j s : ℕ) :
    1 / ((j : ℂ) + 1 / 2) ^ s = 2 ^ s * (1 / (2 * (j : ℂ) + 1) ^ s) := by
  rw [show (j : ℂ) + 1 / 2 = (2 * j + 1) / 2 by ring, div_pow, one_div_div, mul_one_div]

private lemma hasSum_nat_inv_pow {s : ℕ} (hs : 1 < s) :
    HasSum (fun n : ℕ ↦ 1 / (n : ℂ) ^ s) (riemannZeta s) := by
  have h : Summable (fun n : ℕ ↦ 1 / (n : ℂ) ^ s) := by
    simpa using Complex.summable_ofReal.mpr (Real.summable_one_div_nat_pow.mpr hs)
  rw [zeta_nat_eq_tsum_of_gt_one hs]
  simpa [one_div] using h.hasSum

private lemma hasSum_succ_inv_pow {s : ℕ} (hs : 1 < s) :
    HasSum (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ s) (riemannZeta s) := by
  have h := (hasSum_nat_add_iff' 1).2 (hasSum_nat_inv_pow hs)
  simpa [zero_pow (by omega : s ≠ 0)] using h

private lemma hasSum_half_inv_pow {s : ℕ} (hs : 1 < s) :
    HasSum (fun n : ℕ ↦ 1 / ((n : ℂ) + 1 / 2) ^ s) ((2 ^ s - 1) * riemannZeta s) := by
  let f (n : ℕ) : ℂ := 1 / (n : ℂ) ^ s
  have hall : HasSum f (riemannZeta s) := hasSum_nat_inv_pow hs
  have he : HasSum (fun n ↦ f (2 * n)) (((2 : ℂ) ^ s)⁻¹ * riemannZeta s) := by
    apply (hall.mul_left (((2 : ℂ) ^ s)⁻¹)).congr_fun
    intro n
    simp [f, Nat.cast_mul, mul_pow, mul_inv_rev, one_div, mul_comm]
  have ho : Summable (fun n ↦ f (2 * n + 1)) :=
    hall.summable.comp_injective (i := fun n : ℕ ↦ 2 * n + 1) (by intro a b h; dsimp at h; omega)
  have heo := (he.even_add_odd ho.hasSum).unique hall
  have hoVal : (∑' n, f (2 * n + 1)) =
      riemannZeta s - ((2 : ℂ) ^ s)⁻¹ * riemannZeta s := by
    linear_combination heo
  have hov : HasSum (fun n ↦ f (2 * n + 1))
      (riemannZeta s - ((2 : ℂ) ^ s)⁻¹ * riemannZeta s) := by
    rw [← hoVal]
    exact ho.hasSum
  have hhalf : HasSum (fun n : ℕ ↦ 1 / ((n : ℂ) + 1 / 2) ^ s)
      (2 ^ s * (riemannZeta s - ((2 : ℂ) ^ s)⁻¹ * riemannZeta s)) := by
    refine (hov.mul_left (2 ^ s)).congr_fun fun n ↦ ?_
    rw [half_inv_pow]
    simp [f, Nat.cast_add, Nat.cast_mul]
  have hz : (2 : ℂ) ^ s ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hz, ← sub_mul] at hhalf
  exact hhalf

private lemma digamma_nat_add_half (k : ℕ) :
    Complex.digamma (k + 1 / 2) + Real.eulerMascheroniConstant =
      2 * ∑ j ∈ range k, 1 / (2 * (j : ℂ) + 1) - 2 * Complex.log 2 := by
  have hp (n : ℕ) : (1 / 2 : ℂ) ≠ -(n : ℂ) := by
    intro h
    have hpos : 0 < (1 / 2 : ℂ).re := by norm_num [Complex.div_re, Complex.normSq_apply]
    rw [h, Complex.neg_re, Complex.natCast_re] at hpos
    exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg n))) hpos
  have hterm (j : ℕ) : (1 / 2 + (j : ℂ))⁻¹ = 2 * (1 / (2 * (j : ℂ) + 1)) := by
    rw [add_comm (1 / 2 : ℂ) (j : ℂ)]
    simpa only [one_div, pow_one] using half_inv_pow j 1
  rw [add_comm (k : ℂ), Complex.digamma_apply_add_nat hp, Complex.digamma_one_half]
  simp_rw [hterm, ← mul_sum]
  ring

/-- **Harmonic numbers of half-integer index.** Let $k$ be a natural number. For each integer
$r \ge 1$ let $O^{(r)}_k = \sum_{j=1}^{k} \frac{1}{(2j - 1)^r}$, and let $O_k = O^{(1)}_k$.
Let $\psi$ be the digamma function, $\gamma$ the Euler–Mascheroni constant and $\zeta$ the
Riemann zeta function. Then
$$\psi\bigl(k + \tfrac12\bigr) + \gamma = 2 O_k - 2 \log 2,$$
$$\sum_{j=0}^{\infty} \Bigl(\frac{1}{(j + 1)^2} - \frac{1}{(j + k + \frac12)^2}\Bigr) =
-2 \zeta(2) + 4 O^{(2)}_k,$$
$$\sum_{j=0}^{\infty} \Bigl(\frac{1}{(j + 1)^3} - \frac{1}{(j + \frac12)^3}\Bigr) = -6 \zeta(3),$$
and for every natural number $m$,
$$\sum_{j=0}^{\infty} \Bigl(\frac{1}{(j+\frac12)^{m+1}} - \frac{1}{(j+k+\frac12)^{m+1}}\Bigr) =
2^{m+1} O^{(m+1)}_k.$$

With $H_\alpha = \psi(\alpha + 1) + \gamma$ and
$H^{(r)}_\alpha = \sum_{j \ge 1} (j^{-r} - (j + \alpha)^{-r})$, these read
$H_{k-1/2} = 2O_k - 2\log 2$, $H^{(2)}_{k-1/2} = -2\zeta(2) + 4O^{(2)}_k$,
$H^{(3)}_{-1/2} = -6\zeta(3)$ and $H^{(m+1)}_{k-1/2} - H^{(m+1)}_{-1/2} = 2^{m+1} O^{(m+1)}_k$.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Lemma 1 (`integers-2025-A18-lem-1`). -/
public theorem harmonic_nat_sub_half_values (k : ℕ) :
    Complex.digamma (k + 1 / 2) + Real.eulerMascheroniConstant =
        2 * ∑ j ∈ Finset.range k, 1 / (2 * (j : ℂ) + 1) - 2 * Complex.log 2 ∧
      ∑' j : ℕ, (1 / ((j : ℂ) + 1) ^ 2 - 1 / ((j : ℂ) + k + 1 / 2) ^ 2) =
        -2 * riemannZeta 2 + 4 * ∑ j ∈ Finset.range k, 1 / (2 * (j : ℂ) + 1) ^ 2 ∧
      ∑' j : ℕ, (1 / ((j : ℂ) + 1) ^ 3 - 1 / ((j : ℂ) + 1 / 2) ^ 3) = -6 * riemannZeta 3 ∧
      ∀ m : ℕ, ∑' j : ℕ, (1 / ((j : ℂ) + 1 / 2) ^ (m + 1) - 1 / ((j : ℂ) + k + 1 / 2) ^ (m + 1)) =
        2 ^ (m + 1) * ∑ j ∈ Finset.range k, 1 / (2 * (j : ℂ) + 1) ^ (m + 1) := by
  refine ⟨digamma_nat_add_half k, ?_, ?_, ?_⟩
  · have h := ((hasSum_succ_inv_pow (s := 2) (by decide)).sub
      (hasSum_half_inv_pow (s := 2) (by decide))).add (hasSum_half_pow_sub_shift k 1)
    rw [(h.congr_fun (fun j ↦ by dsimp; ring)).tsum_eq]
    simp_rw [half_inv_pow, ← mul_sum]
    norm_num
    ring
  · rw [((hasSum_succ_inv_pow (s := 3) (by decide)).sub
      (hasSum_half_inv_pow (s := 3) (by decide))).tsum_eq]
    norm_num
    ring
  · intro m
    rw [(hasSum_half_pow_sub_shift k m).tsum_eq, mul_sum]
    exact sum_congr rfl (fun j _ ↦ half_inv_pow j (m + 1))

end MetaMathlibExt
