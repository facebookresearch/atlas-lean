/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import MathlibExt.Combinatorics.Enumerative.PentagonalNumber

/-!
# Parity of Euler's pentagonal recurrence

We take a coefficient of Euler's identity for the partition generating function and reduce it
modulo two, so that the signs in the recurrence can be dropped.
-/

open Finset PowerSeries

namespace MetaMathlibExt

private theorem mem_Icc_of_pentagonal_neg_le {n : ℕ} {k : ℤ} (hk : pentagonal (-k) ≤ n) :
    k ∈ Icc (-(n : ℤ)) n := by
  rw [mem_Icc]
  have hcast : (pentagonal (-k) : ℤ) ≤ n := by exact_mod_cast hk
  have hp := two_mul_natCast_pentagonal_neg k
  rcases lt_trichotomy k 0 with h | rfl | h
  · have h' : 0 ≤ -3 * k - 3 := by omega
    exact ⟨by nlinarith [mul_nonneg (neg_nonneg.mpr h.le) h'], by omega⟩
  · omega
  · have h' : 0 ≤ 3 * k - 1 := by omega
    exact ⟨by omega, by nlinarith [mul_nonneg h.le h']⟩

private theorem cast_pentagonal_neg (k : ℤ) :
    (pentagonal (-k) : ℤ) = k * (3 * k + 1) / 2 := by
  rw [natCast_pentagonal]
  congr 1
  ring

/-- **Parity form of Euler's pentagonal recurrence.** Write $p(m)$ for the number of partitions
of $m$. For every positive integer $n$, the sum
$\sum_{k \in \mathbb{Z},\ k(3k+1)/2 \le n} p(n - k(3k+1)/2)$ is even.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Corollary 2 (`integers-2026-A60-cor-2`). -/
public theorem partition_pentagonal_sum_even (n : ℕ) (hn : 0 < n) :
    Even (∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) / 2 ≤ (n : ℤ)),
      Fintype.card (Nat.Partition (n - (k * (3 * k + 1) / 2).toNat))) := by
  have hcoeff : ∑ i ∈ range (n + 1), ((pentagonalSeries ℤ).coeff i : ZMod 2) *
      (partitionFunction (n - i) : ZMod 2) = 0 := by
    have h := congrArg (coeff n) mk_partitionFunction_mul_pentagonalSeries
    rw [mul_comm _ (pentagonalSeries ℤ), coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      coeff_one, ite_eq_right hn.ne'] at h
    simpa only [Int.cast_sum, Int.cast_mul, coeff_mk, Int.cast_natCast, Int.cast_zero]
      using congrArg (fun x : ℤ => (x : ZMod 2)) h
  simp only [← cast_pentagonal_neg, Int.toNat_natCast, Nat.cast_le,
    ← ZMod.natCast_eq_zero_iff_even, Nat.cast_sum]
  let s := (Icc (-(n : ℤ)) n).filter (fun k : ℤ => pentagonal (-k) ≤ n)
  change ∑ k ∈ s, (partitionFunction (n - pentagonal (-k)) : ZMod 2) = 0
  refine (sum_of_injOn (fun k => pentagonal (-k))
    (pentagonal_injective.comp neg_injective).injOn ?_ ?_ ?_).trans hcoeff
  · intro k hk
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hk).2)
  · intro i hiRange hi
    suffices i ∉ Set.range pentagonal by
      rw [coeff_pentagonalSeries_eq_zero ℤ this, Int.cast_zero, zero_mul]
    rintro ⟨k, rfl⟩
    have hk : pentagonal (-(-k)) ≤ n := by
      simpa only [neg_neg] using Nat.le_of_lt_succ (mem_range.mp hiRange)
    exact hi ⟨-k, mem_filter.mpr ⟨mem_Icc_of_pentagonal_neg_le hk, hk⟩, by simp⟩
  · intro k _
    rw [coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow, Int.cast_pow, Int.cast_neg,
      Int.cast_one, ZMod.neg_one_eq_one_iff.mpr (Or.inr rfl), one_pow, one_mul]

end MetaMathlibExt
