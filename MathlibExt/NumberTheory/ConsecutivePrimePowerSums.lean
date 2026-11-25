/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.PrimeCounting

/-!
# Sums of powers of consecutive primes

`card_consecutivePrimePowerSums_length_le` bounds the number of sums of a fixed length
by counting their possible starting primes.
-/

namespace MetaMathlibExt

open Finset

/-- **Counting sums of a fixed number of consecutive prime powers.** Let $p_1 < p_2 < \cdots$
be the primes. For natural numbers $k > 1$, $m > 0$ and $x$, the number of integers $n \le x$ of
the form $n = p_{\ell+1}^k + p_{\ell+2}^k + \cdots + p_{\ell+m}^k$ for some $\ell \ge 0$ is at
most $\pi(\lfloor (x/m)^{1/k} \rfloor)$, the number of primes up to $(x/m)^{1/k}$.

Source: Cathal O'Sullivan, Jonathan P. Sorenson, and Aryn Stahl, *Algorithms and Bounds on the
Sums of Powers of Consecutive Primes*, INTEGERS 24 (2024), Article A4, Lemma 1 (quoted from
[6]) (`integers-2024-A4-lem-1`). -/
public theorem card_consecutivePrimePowerSums_length_le (k m x : ℕ) (hk : 1 < k)
    (hm : 0 < m) :
    {n : ℕ | n ≤ x ∧ ∃ l, n = ∑ i ∈ range m, Nat.nth Nat.Prime (l + i) ^ k}.ncard ≤
      Nat.primeCounting ⌊((x : ℝ) / m) ^ ((1 : ℝ) / k)⌋₊ := by
  let block (l : ℕ) := ∑ i ∈ range m, Nat.nth Nat.Prime (l + i) ^ k
  let cutoff := ⌊((x : ℝ) / m) ^ ((1 : ℝ) / k)⌋₊
  have start_lt (l : ℕ) (hl : block l ≤ x) : l < cutoff.primeCounting := by
    have hmin : Nat.nth Nat.Prime l ^ k * m ≤ x := calc
      _ = ∑ _i ∈ range m, Nat.nth Nat.Prime l ^ k := by simp [Nat.mul_comm]
      _ ≤ block l := by
        apply sum_le_sum
        intro i _
        exact Nat.pow_le_pow_left (Nat.nth_monotone Nat.infinite_setOfPred_prime
          (Nat.le_add_right l i)) k
      _ ≤ x := hl
    apply (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).mpr
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    rw [one_div, Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
      (by exact_mod_cast Nat.zero_lt_of_lt hk), Real.rpow_natCast]
    apply (le_div_iff₀ (by exact_mod_cast hm)).mpr
    exact_mod_cast hmin
  calc
    _ ≤ (↑((range cutoff.primeCounting).image block) : Set ℕ).ncard := by
      refine Set.ncard_le_ncard ?_ (Finset.finite_toSet _)
      rintro n ⟨hn, l, rfl⟩
      exact mem_image.mpr ⟨l, mem_range.mpr (start_lt l hn), rfl⟩
    _ ≤ cutoff.primeCounting := by
      simpa only [Set.ncard_coe_finset, card_range] using
        (card_image_le (s := range cutoff.primeCounting) (f := block))

end MetaMathlibExt
