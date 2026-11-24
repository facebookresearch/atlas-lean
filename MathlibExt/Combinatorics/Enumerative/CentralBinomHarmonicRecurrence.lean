/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.Enumerative.CentralBinomHarmonicSums
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Recurrence for central binomial sums with harmonic numbers

We telescope the normalized binomial weight multiplied by a shifted harmonic number, then
expand two powers of `k - 1` to express the result in terms of weighted power sums.
-/

namespace MetaMathlibExt

open Finset

private def weight (k : ℕ) : ℚ := (k.centralBinom : ℚ) / 4 ^ k

private def boundary (s : ℚ) (k : ℕ) : ℚ := (2 * (k : ℚ) + 1) * weight k * (harmonic k + s)

private theorem weight_succ_mul (k : ℕ) :
    (2 * (k : ℚ) + 1) * weight k = 2 * ((k + 1 : ℕ) : ℚ) * weight (k + 1) := by
  have h : ((k : ℚ) + 1) * (k + 1).centralBinom = 2 * (2 * (k : ℚ) + 1) * k.centralBinom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  simp only [weight, pow_succ, Nat.cast_add, Nat.cast_one]
  field_simp
  linear_combination -2 * h

-- The shift `s = -2` makes the difference exactly the unweighted harmonic summand.
private theorem boundary_succ_sub (s : ℚ) (k : ℕ) :
    boundary s (k + 1) - boundary s k = weight (k + 1) * (harmonic (k + 1) + (s + 2)) := by
  have hk : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  unfold boundary
  rw [weight_succ_mul k, harmonic_succ]
  field_simp
  ring

private theorem harmonicSum_zero_exp (n : ℕ) :
    centralBinomPowSum harmonic 0 n = boundary (-2) n + 2 := by
  induction n with
  | zero => norm_num [centralBinomPowSum_zero, boundary, weight]
  | succ n ih =>
    rw [centralBinomPowSum_succ, ih]
    simp only [pow_zero, mul_one]
    change boundary (-2) n + 2 + weight (n + 1) * harmonic (n + 1) = _
    linear_combination -(boundary_succ_sub (-2) n)

private theorem weighted_boundary_succ_sub (r k : ℕ) :
    let x : ℚ := (k + 1 : ℕ)
    ((x ^ r + 2 * x * (x ^ r - (x - 1) ^ r)) * harmonic (k + 1) +
      x ^ r + 2 * (x ^ (r + 1) - (x - 1) ^ (r + 1))) * weight (k + 1) =
    x ^ r * boundary 1 (k + 1) - (k : ℚ) ^ r * boundary 1 k := by
  dsimp only
  have hx : ((k + 1 : ℕ) : ℚ) - 1 = (k : ℚ) := by push_cast; ring
  rw [hx, pow_succ ((k + 1 : ℕ) : ℚ), pow_succ (k : ℚ)]
  have h := boundary_succ_sub 1 k
  rw [show boundary 1 k = boundary 1 (k + 1) -
    weight (k + 1) * (harmonic (k + 1) + (1 + 2)) by linear_combination -h, boundary]
  push_cast
  ring

private theorem weighted_telescope (n r : ℕ) (hr : 1 ≤ r) :
    (∑ k ∈ range (n + 1),
      (((k : ℚ) ^ r + 2 * k * ((k : ℚ) ^ r - ((k : ℚ) - 1) ^ r)) * harmonic k +
        (k : ℚ) ^ r + 2 * ((k : ℚ) ^ (r + 1) - ((k : ℚ) - 1) ^ (r + 1))) * weight k) =
    (n : ℚ) ^ r * boundary 1 n + 2 * (-1) ^ r := by
  induction n with
  | zero =>
    have hr₀ : r ≠ 0 := by omega
    simp [weight, zero_pow hr₀, pow_succ (-1 : ℚ) r]
  | succ n ih =>
    rw [sum_range_succ, ih, weighted_boundary_succ_sub]
    ring

private theorem shifted_pow_sub (x : ℚ) (r : ℕ) :
    x ^ (r + 1) - (x - 1) ^ (r + 1) = ∑ j ∈ range (r + 1),
      ((r + 1).choose j : ℚ) * (-1) ^ (r - j) * x ^ j := by
  rw [sub_eq_add_neg x 1, add_pow, sum_range_succ]
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one]
  rw [sub_add_eq_sub_sub, sub_right_comm, sub_self, zero_sub, ← sum_neg_distrib]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.mp hj
  rw [show r + 1 - j = (r - j) + 1 by omega, pow_succ (-1 : ℚ) (r - j)]
  ring

private theorem harmonicKernel (x : ℚ) (r : ℕ) (hr : 1 ≤ r) :
    x ^ r + 2 * x * (x ^ r - (x - 1) ^ r) = (2 * (r : ℚ) + 1) * x ^ r -
      2 * ∑ j ∈ Icc 1 (r - 1), (r.choose (j + 1) : ℚ) * (-1) ^ (j + 1) * x ^ (r - j) := by
  cases r with
  | zero => omega
  | succ r =>
    let f : ℕ → ℚ := fun j => ((r + 1).choose j : ℚ) * (-1) ^ j * x ^ (r + 1 - j)
    have hex : (x - 1) ^ (r + 1) = ∑ j ∈ range (r + 1 + 1), f j := by
      rw [show x - 1 = -1 + x by ring, add_pow]
      exact sum_congr rfl fun j _ => by dsimp [f]; ring
    rw [hex, sum_range_succ' f, sum_range_succ' (fun j => f (j + 1))]
    have hIcc : Icc 1 r = Ico 1 (r + 1) := by
      ext j
      simp only [mem_Icc, mem_Ico]
      omega
    have htail : x * (∑ j ∈ range r, f (j + 1 + 1)) =
        ∑ j ∈ Icc 1 r, ((r + 1).choose (j + 1) : ℚ) * (-1) ^ (j + 1) * x ^ (r + 1 - j) := by
      rw [hIcc, sum_Ico_eq_sum_range, mul_sum, Nat.add_sub_cancel]
      refine sum_congr rfl fun j hj => ?_
      have hj' := mem_range.mp hj
      dsimp [f]
      rw [show j + 1 + 1 = 1 + j + 1 by omega,
        show r + 1 - (1 + j) = (r + 1 - (1 + j + 1)) + 1 by omega,
        pow_succ x (r + 1 - (1 + j + 1))]
      ring
    simp only [show r.succ - 1 = r from Nat.succ_sub_one r, Nat.cast_succ]
    rw [← htail]
    simp only [f, zero_add, Nat.choose_zero_right, Nat.choose_one_right, Nat.sub_zero,
      Nat.add_sub_cancel, pow_zero, pow_one, Nat.cast_one, Nat.cast_add, one_mul, mul_one]
    ring

private theorem sum_weighted_pow (a : ℕ → ℚ) (n : ℕ) (s : Finset ℕ) (b : ℕ → ℚ) (e : ℕ → ℕ) :
    (∑ k ∈ range (n + 1), weight k * ((∑ j ∈ s, b j * (k : ℚ) ^ e j) * a k)) =
      ∑ j ∈ s, b j * centralBinomPowSum a (e j) n := by
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  simp only [centralBinomPowSum, weight, mul_sum]
  exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring

/-- **Recurrence for central binomial sums with harmonic numbers.** For a natural number $n$,
let $H_m = \sum_{i=1}^{m} 1/i$ be the harmonic numbers, $c_n = \binom{2n}{n}/4^n$, and for natural
$r$ let $S_r(n) = \sum_{k=0}^{n} \binom{2k}{k} 4^{-k} k^r$ and
$S_r^H(n) = \sum_{k=0}^{n} \binom{2k}{k} 4^{-k} k^r H_k$, with $0^0 = 1$. Then
$$S_0^H(n) = (2n+1)\, c_n (H_n - 2) + 2,$$
and for every $r \ge 1$
$$(2r+1) S_r^H(n) = n^r (2n+1)\, c_n (H_n + 1) + 2(-1)^r - S_r(n) +
2 \sum_{j=1}^{r-1} \binom{r}{j+1} (-1)^{j+1} S_{r-j}^H(n) -
2 \sum_{j=0}^{r} \binom{r+1}{j} (-1)^{r-j} S_j(n).$$

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Theorem 2 (`integers-2026-A109-thm-2`). -/
public theorem centralBinomPowSum_harmonic_recursion (n : ℕ) :
    centralBinomPowSum harmonic 0 n =
        (2 * n + 1) * ((n.centralBinom : ℚ) / 4 ^ n) * (harmonic n - 2) + 2 ∧
      ∀ r : ℕ, 1 ≤ r →
        (2 * r + 1) * centralBinomPowSum harmonic r n =
          (n : ℚ) ^ r * (2 * n + 1) * ((n.centralBinom : ℚ) / 4 ^ n) * (harmonic n + 1) +
              2 * (-1) ^ r - centralBinomPowSum 1 r n +
            2 * ∑ j ∈ Icc 1 (r - 1),
              ((r.choose (j + 1) : ℕ) : ℚ) * (-1) ^ (j + 1) *
                centralBinomPowSum harmonic (r - j) n -
            2 * ∑ j ∈ range (r + 1),
              (((r + 1).choose j : ℕ) : ℚ) * (-1) ^ (r - j) * centralBinomPowSum 1 j n := by
  refine ⟨by simpa [boundary, weight, sub_eq_add_neg] using harmonicSum_zero_exp n, ?_⟩
  intro r hr
  let b : ℕ → ℚ := fun j => (r.choose (j + 1) : ℚ) * (-1) ^ (j + 1)
  let d : ℕ → ℚ := fun j => ((r + 1).choose j : ℚ) * (-1) ^ (r - j)
  have he (k : ℕ) :
      (((k : ℚ) ^ r + 2 * k * ((k : ℚ) ^ r - ((k : ℚ) - 1) ^ r)) * harmonic k +
        (k : ℚ) ^ r + 2 * ((k : ℚ) ^ (r + 1) - ((k : ℚ) - 1) ^ (r + 1))) * weight k =
      (2 * (r : ℚ) + 1) * (weight k * (k : ℚ) ^ r * harmonic k) -
        2 * (weight k * ((∑ j ∈ Icc 1 (r - 1), b j * (k : ℚ) ^ (r - j)) * harmonic k)) +
        weight k * (k : ℚ) ^ r * (1 : ℕ → ℚ) k +
        2 * (weight k * ((∑ j ∈ range (r + 1), d j * (k : ℚ) ^ j) * (1 : ℕ → ℚ) k)) := by
    rw [harmonicKernel _ r hr, shifted_pow_sub]
    dsimp only [b, d, Pi.one_apply]
    ring
  have ht := weighted_telescope n r hr
  simp_rw [he, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_weighted_pow] at ht
  change (2 * (r : ℚ) + 1) * centralBinomPowSum harmonic r n -
      2 * (∑ j ∈ Icc 1 (r - 1), b j * centralBinomPowSum harmonic (r - j) n) +
      centralBinomPowSum 1 r n + 2 * (∑ j ∈ range (r + 1), d j * centralBinomPowSum 1 j n) =
      (n : ℚ) ^ r * boundary 1 n + 2 * (-1) ^ r at ht
  dsimp only [boundary, weight, b, d] at ht
  linear_combination ht

end MetaMathlibExt
