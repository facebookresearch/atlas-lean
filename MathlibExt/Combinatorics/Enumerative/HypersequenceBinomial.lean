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
import Mathlib.Algebra.BigOperators.Intervals

/-! # Binomial formulas for hypersequences

Parisse's two formulas for a complex sequence follow from Pascal's identity
and reflection of the finite sum.
-/

namespace MetaMathlibExt

open Finset

private theorem hypersequence_binomial_first (a : ℕ → ℂ) (s n : ℕ) :
    hypersequence a (s + 1) n =
      ∑ k ∈ range (n + 1), ((n + s - k).choose s : ℂ) * a k := by
  induction s generalizing n with
  | zero => simp [hypersequence]
  | succ s ih =>
    induction n with
    | zero =>
      rw [hypersequence_succ a (s + 1) 0, sum_range_one, ih 0]
      simp
    | succ n ihN =>
      have step : hypersequence a (s + 1 + 1) (n + 1) =
          hypersequence a (s + 1 + 1) n + hypersequence a (s + 1) (n + 1) := by
        calc
          _ = (∑ k ∈ range (n + 1), hypersequence a (s + 1) k) +
                hypersequence a (s + 1) (n + 1) := by
              rw [hypersequence_succ a (s + 1) (n + 1), sum_range_succ]
          _ = _ := by rw [hypersequence_succ a (s + 1) n]
      change hypersequence a (s + 1 + 1) (n + 1) =
        ∑ k ∈ range (n + 1 + 1), ((n + 1 + (s + 1) - k).choose (s + 1) : ℂ) * a k
      rw [step, ihN, ih (n + 1)]
      simp only [sum_range_succ _ (n + 1)]
      rw [← add_assoc, ← sum_add_distrib]
      congr 1
      · apply sum_congr rfl
        intro k hk
        have hkn := mem_range.mp hk
        have htop : n + 1 + (s + 1) - k = (n + 1 + s - k).succ := by omega
        have hprev : n + s.succ - k = n + 1 + s - k := by omega
        rw [htop, hprev, Nat.choose_succ_succ, Nat.cast_add, add_mul, add_comm]
      · have h₁ : n + 1 + s - (n + 1) = s := by omega
        have h₂ : n + 1 + (s + 1) - (n + 1) = s + 1 := by omega
        simp [h₁, h₂]

/-- **Hypersequences as binomial sums.** Let $(a_n)$ be a sequence of complex numbers and let
$a^{(r)}_n$ denote its hypersequence of generation $r$. For every $r \ge 1$ and every natural
number $n$,
$$a^{(r)}_n = \sum_{k=0}^{n} \binom{n+r-1-k}{r-1} a_k = \sum_{k=0}^{n} \binom{r+k-1}{k} a_{n-k}.$$

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 1, Equation (2.1) (`integers-2024-A70-thm-1`). -/
public theorem hypersequence_eq_sum_choose (a : ℕ → ℂ) {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    hypersequence a r n = ∑ k ∈ range (n + 1), ((n + r - 1 - k).choose (r - 1) : ℂ) * a k ∧
      hypersequence a r n = ∑ k ∈ range (n + 1), ((r + k - 1).choose k : ℂ) * a (n - k) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have h := hypersequence_binomial_first a s n
  have h₁ : n + (s + 1) - 1 = n + s := by omega
  have h₂ : s + 1 - 1 = s := by omega
  refine ⟨by simpa only [h₁, h₂] using h, ?_⟩
  rw [h, ← sum_flip (n := n) (fun k ↦ ((n + s - k).choose s : ℂ) * a k)]
  apply sum_congr rfl
  intro k hk
  have hkn := mem_range.mp hk
  have htop : n + s - (n - k) = s + k := by omega
  have hrhs : s + 1 + k - 1 = s + k := by omega
  rw [htop, hrhs, Nat.choose_symm_of_eq_add (n := s + k) (a := s) (b := k) rfl]

end MetaMathlibExt
