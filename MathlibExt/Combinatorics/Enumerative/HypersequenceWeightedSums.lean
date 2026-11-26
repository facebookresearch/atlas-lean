/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Combinatorics.Enumerative.Hypersequence
import Mathlib.Data.Nat.Choose.Sum
import MathlibExt.Combinatorics.Enumerative.HypersequenceAbelSummation

/-! # Recurrence for power-weighted sums of hypersequences -/

namespace MetaMathlibExt

open Finset

/-- **Recurrence for power-weighted sums of hypersequences.** Let $a$ be a sequence of complex
numbers, let $a^{(r)}_k$ denote its hypersequence of generation $r$, and for natural numbers
$\ell$, $r$ and $n$ let $t^{(r)}_\ell(n) = \sum_{k=0}^{n} k^\ell a^{(r)}_k$, with the convention
$0^0 = 1$. Then for all natural numbers $\ell$, $r$ and $n$,
$$t^{(r)}_\ell(n) = (n + 1)^\ell a^{(r+1)}_n - \sum_{j=0}^{\ell-1} \binom{\ell}{j} t^{(r+1)}_j(n),$$
where the sum over $j$ is empty when $\ell = 0$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 8, Equation (3.5) (`integers-2024-A70-thm-8`). -/
public theorem sum_pow_mul_hypersequence_recurrence (a : ℕ → ℂ) (ℓ r n : ℕ) :
    ∑ k ∈ range (n + 1), (k : ℂ) ^ ℓ * hypersequence a r k =
      ((n : ℂ) + 1) ^ ℓ * hypersequence a (r + 1) n -
        ∑ j ∈ range ℓ, (ℓ.choose j : ℂ) *
          ∑ k ∈ range (n + 1), (k : ℂ) ^ j * hypersequence a (r + 1) k := by
  have hprefix (k : ℕ) :
      hypersequence (hypersequence a r) 1 k = hypersequence a (r + 1) k := by
    calc
      _ = ∑ i ∈ range (k + 1), hypersequence a r i := hypersequence_succ _ 0 k
      _ = _ := (hypersequence_succ a r k).symm
  have hdiff (x : ℂ) : (x + 1) ^ ℓ - x ^ ℓ = ∑ j ∈ range ℓ, (ℓ.choose j : ℂ) * x ^ j := by
    -- The degree-ℓ term cancels, leaving the sum empty when ℓ = 0.
    rw [add_pow, sum_range_succ]
    simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one, add_sub_cancel_right]
    exact sum_congr rfl fun j _ => mul_comm _ _
  calc
    _ = ∑ k ∈ range (n + 1), hypersequence a r k * (k : ℂ) ^ ℓ :=
      sum_congr rfl fun k _ => mul_comm _ _
    _ = ((n : ℂ) + 1) ^ ℓ * hypersequence a (r + 1) n -
        ∑ k ∈ range (n + 1),
          (((k : ℂ) + 1) ^ ℓ - (k : ℂ) ^ ℓ) * hypersequence a (r + 1) k := by
      rw [sum_mul_eq_hypersequence_one_mul_add_sum (hypersequence a r) (fun k => (k : ℂ) ^ ℓ)]
      simp only [hprefix, Nat.cast_add, Nat.cast_one, mul_comm (hypersequence a (r + 1) n)]
      conv_rhs => rw [sub_eq_add_neg, ← sum_neg_distrib]
      congr 1
      exact sum_congr rfl fun k _ => by rw [← neg_mul, neg_sub, mul_comm]
    _ = _ := by
      simp only [hdiff, sum_mul]
      rw [sum_comm]
      congr 1
      exact sum_congr rfl fun j _ => by
        rw [mul_sum]
        exact sum_congr rfl fun k _ => by ac_rfl

end MetaMathlibExt
