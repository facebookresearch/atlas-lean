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
# Sum of a periodic sequence

`MetaMathlibExt.sum_Icc_of_periodic` expresses a partial sum as its length times the period
average plus the sum of the deviations over the remaining terms.
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

end MetaMathlibExt
