/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Nat.Periodic

/-!
# Sums of periodic sequences

`MetaMathlibExt.sum_Icc_of_periodic` expresses a partial sum as its length times the period
average plus the sum of the deviations over the remaining terms.
`MetaMathlibExt.sum_Icc_of_eventually_periodic` applies the same formula to the tail of an
eventually periodic sequence and adds the initial prefix sum.
-/

open Finset

namespace MetaMathlibExt

/-- **Sum of a periodic sequence.** Let $K$ be a field of characteristic zero, let
$f : \mathbb{N} \to K$ and let $L \ge 1$ be a natural number such that $f(i + L) = f(i)$ for
all $i \ge 1$. Let $\bar f = \frac{1}{L} \sum_{k=1}^{L} f(k)$. Then for every natural number $N$,
$$\sum_{i=1}^{N} f(i) = N \bar f + \sum_{k=1}^{N \bmod L} \left(f(k) - \bar f\right).$$

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 1 (Sum of a periodic sequence) (`integers-2026-A78-lem-1`). -/
public theorem sum_Icc_of_periodic {K : Type*} [Field K] [CharZero K] (f : ℕ → K)
    {L : ℕ} (hL : 0 < L) (hf : ∀ i, 1 ≤ i → f (i + L) = f i) (N : ℕ) :
    ∑ i ∈ Icc 1 N, f i =
      N * ((∑ k ∈ Icc 1 L, f k) / L) +
        ∑ k ∈ Icc 1 (N % L), (f k - (∑ k ∈ Icc 1 L, f k) / L) := by
  let avg := (∑ k ∈ Icc 1 L, f k) / L
  let S (n : ℕ) := ∑ k ∈ Icc 1 n, (f k - avg)
  have hS (n : ℕ) : S n = (∑ k ∈ Icc 1 n, f k) - n * avg := by
    simp [S, sum_sub_distrib, nsmul_eq_mul]
  have step (n : ℕ) : S (n + 1) = S n + (f (n + 1) - avg) :=
    sum_Icc_succ_top (Nat.succ_pos n) _
  have periodic : Function.Periodic S L := by
    intro n
    induction n with
    | zero =>
      have hL' : (L : K) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
      simp [hS, avg, mul_div_cancel₀ _ hL']
    | succ n ih =>
      rw [Nat.succ_add, step, step n, ih, add_right_comm n L 1, hf _ (Nat.succ_pos n)]
  change _ = N * avg + S (N % L)
  rw [periodic.map_mod_nat, hS, add_sub_cancel]

/-- **Sum of an eventually periodic sequence.** Let $K$ be a field of characteristic zero, let
$f : \mathbb{N} \to K$, and let $L \ge 1$ and $D \ge 1$ be natural numbers such that
$f(i + L) = f(i)$ for all $i \ge D$. Let $\bar f = \frac{1}{L} \sum_{k=D}^{D+L-1} f(k)$ be the
average over one period. Then for every natural number $N \ge D - 1$,
$$\sum_{i=1}^{N} f(i) = \sum_{i=1}^{D-1} f(i) + (N - D + 1) \bar f +
\sum_{k=1}^{(N-D+1) \bmod L} \left(f(k + D - 1) - \bar f\right).$$

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Corollary 1 (Sum of an eventually periodic sequence) (`integers-2026-A78-cor-1`). -/
public theorem sum_Icc_of_eventually_periodic {K : Type*} [Field K] [CharZero K]
    (f : ℕ → K) {L D : ℕ} (hL : 0 < L) (hD : 1 ≤ D) (hf : ∀ i, D ≤ i → f (i + L) = f i)
    {N : ℕ} (hN : D - 1 ≤ N) :
    ∑ i ∈ Icc 1 N, f i =
      ∑ i ∈ Icc 1 (D - 1), f i + ((N + 1 - D : ℕ) : K) * ((∑ k ∈ Ico D (D + L), f k) / L) +
        ∑ k ∈ Icc 1 ((N + 1 - D) % L), (f (k + D - 1) - (∑ k ∈ Ico D (D + L), f k) / L) := by
  let g (i : ℕ) := f (i + (D - 1))
  have hg (i : ℕ) (hi : 1 ≤ i) : g (i + L) = g i := by
    simpa only [g, add_right_comm i L (D - 1)] using hf (i + (D - 1)) (by omega)
  have hstart : 1 + (D - 1) = D := by omega
  have sum_shift (m : ℕ) :
      ∑ i ∈ Icc 1 m, g i = ∑ i ∈ Ico D (m + 1 + (D - 1)), f i := by
    simpa only [Ico_add_one_right_eq_Icc, hstart, g] using
      (sum_Ico_add' f 1 (m + 1) (D - 1))
  have htail := sum_shift (N + 1 - D)
  rw [show N + 1 - D + 1 + (D - 1) = N + 1 by omega] at htail
  have hperiod := sum_shift L
  rw [show L + 1 + (D - 1) = D + L by omega] at hperiod
  calc
    ∑ i ∈ Icc 1 N, f i = (∑ i ∈ Icc 1 (D - 1), f i) + ∑ i ∈ Ico D (N + 1), f i := by
      simpa only [← Ico_add_one_right_eq_Icc, show D - 1 + 1 = D by omega] using
        (sum_Ico_consecutive f hD (show D ≤ N + 1 by omega)).symm
    _ = _ := by
      rw [← htail, sum_Icc_of_periodic g hL hg, hperiod, ← add_assoc]
      simp only [g, Nat.add_sub_assoc hD]

end MetaMathlibExt
