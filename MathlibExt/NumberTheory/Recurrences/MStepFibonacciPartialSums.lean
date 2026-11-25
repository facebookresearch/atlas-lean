/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Partial sums of `m`-step Fibonacci numbers

The `m`-step Fibonacci numbers of Bates, Morrison, Rogers, Serafini and Sood enter as a function
`F : ℕ → ℕ` with `F 0 = 1`, `F k = 2 ^ (k - 1)` for `1 ≤ k ≤ m - 1`, and
`F k = F (k - 1) + ⋯ + F (k - m)` for `k ≥ m`. Their partial sums `S n = F 0 + ⋯ + F n` are
characterized by the initial values `S n = 2 ^ n` for `n ≤ m` and the recurrence
`S n = 2 * S (n - 1) - S (n - m - 1)` for `n ≥ m + 1`.

## Main results

* `MetaMathlibExt.sum_mStepFibonacci_iff_recurrence`: a real sequence is the sequence of these
  partial sums if and only if it has these initial values and satisfies this recurrence.

## References

* Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood, *A New Combinatorial
  Interpretation of Partial Sums of m-Step Fibonacci Numbers*, Journal of Integer Sequences 28
  (2025), Article 25.6.6; Lemma 2.6 of the arXiv version `2503.11055v1`.
-/

namespace MetaMathlibExt

/-- A window of `m` consecutive terms ending just before `k` is a difference of two partial
sums: `F (k - 1) + ⋯ + F (k - m) + (F 0 + ⋯ + F (k - m - 1)) = F 0 + ⋯ + F (k - 1)`. -/
private theorem sum_Icc_sub_add_sum_range (F : ℕ → ℕ) :
    ∀ m k : ℕ, m ≤ k →
      ∑ t ∈ Finset.Icc 1 m, (F (k - t) : ℝ) + ∑ j ∈ Finset.range (k - m), (F j : ℝ) =
        ∑ j ∈ Finset.range k, (F j : ℝ)
  | 0, k, _ => by simp
  | m + 1, k, h => by
    rw [Finset.sum_Icc_succ_top (by omega), ← sum_Icc_sub_add_sum_range F m k (by omega),
      show k - m = k - (m + 1) + 1 by omega, Finset.sum_range_succ]
    ring

/-- **Recurrence for partial sums of $m$-step Fibonacci numbers.** Let $m \ge 1$ and let
$F : \mathbb{N} \to \mathbb{N}$ satisfy $F(0) = 1$, $F(k) = 2^{k-1}$ for $1 \le k \le m - 1$,
and $F(k) = F(k-1) + \cdots + F(k-m)$ for $k \ge m$ (the $m$-step Fibonacci numbers). Then a
real sequence $(S_n)_{n \ge 0}$ satisfies $S_n = F(0) + F(1) + \cdots + F(n)$ for all $n$ if
and only if $S_n = 2^n$ for $0 \le n \le m$ and $S_n = 2 S_{n-1} - S_{n-m-1}$ for $n \ge m + 1$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Lemma 9
(`jis-2025-25.6.6-lem-9`). -/
public theorem sum_mStepFibonacci_iff_recurrence
    (m : ℕ) (hm : 1 ≤ m) (F : ℕ → ℕ) (hF0 : F 0 = 1)
    (hFinit : ∀ k, 1 ≤ k → k ≤ m - 1 → F k = 2 ^ (k - 1))
    (hFrec : ∀ k, m ≤ k → F k = ∑ t ∈ Finset.Icc 1 m, F (k - t)) (S : ℕ → ℝ) :
    (∀ n, S n = ∑ j ∈ Finset.range (n + 1), (F j : ℝ)) ↔
      ((∀ n, n ≤ m → S n = 2 ^ n) ∧ ∀ n, m + 1 ≤ n → S n = 2 * S (n - 1) - S (n - m - 1)) := by
  set P : ℕ → ℝ := fun n => ∑ j ∈ Finset.range (n + 1), (F j : ℝ) with hP
  have hFrecR : ∀ k, m ≤ k → (F k : ℝ) = ∑ t ∈ Finset.Icc 1 m, (F (k - t) : ℝ) := by
    intro k hk
    rw [hFrec k hk, Nat.cast_sum]
  -- The partial sums start with the powers of two `P 0, …, P m`.
  have hinit : ∀ n, n ≤ m → P n = 2 ^ n := by
    intro n
    induction n with
    | zero => simp [hP, hF0]
    | succ n ih =>
      intro hn
      have hFn : (F (n + 1) : ℝ) = 2 ^ n := by
        rcases Nat.lt_or_ge (n + 1) m with h | h
        · exact_mod_cast hFinit (n + 1) (by omega) (by omega)
        · -- At `n + 1 = m`, `F m = F 0 + ⋯ + F (m - 1) = P n`.
          have hm' : m = n + 1 := by omega
          have key := sum_Icc_sub_add_sum_range F m m le_rfl
          rw [Nat.sub_self, Finset.range_zero, Finset.sum_empty, add_zero, ← hFrecR m le_rfl,
            hm'] at key
          rw [key, ← ih (by omega)]
      simp only [hP] at ih ⊢
      rw [Finset.sum_range_succ, ih (by omega), hFn, pow_succ]
      ring
  -- Beyond `m`, `P n = P (n - 1) + F n` and `F n = P (n - 1) - P (n - m - 1)`.
  have hrec : ∀ n, m + 1 ≤ n → P n = 2 * P (n - 1) - P (n - m - 1) := by
    intro n hn
    have key := sum_Icc_sub_add_sum_range F m n (by omega)
    rw [← hFrecR n (by omega)] at key
    simp only [hP]
    rw [show n - 1 + 1 = n by omega, show n - m - 1 + 1 = n - m by omega, Finset.sum_range_succ]
    linarith
  constructor
  · intro hS
    obtain rfl : S = P := funext hS
    exact ⟨hinit, hrec⟩
  · -- Both sequences have the same initial values and recurrence, so they agree.
    rintro ⟨hSinit, hSrec⟩ n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      change S n = P n
      rcases Nat.lt_or_ge m n with h | h
      · rw [hSrec n h, hrec n h, ih (n - 1) (by omega), ih (n - m - 1) (by omega)]
      · rw [hSinit n h, hinit n h]

end MetaMathlibExt
