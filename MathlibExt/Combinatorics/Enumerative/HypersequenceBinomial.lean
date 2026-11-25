/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import MathlibExt.Combinatorics.Enumerative.Hypersequence
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum

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

-- The Lucas recurrence telescopes over a shifted prefix sum.
private theorem lucasNumber_add_two_eq_sum (m n : ℕ) :
    lucasNumber (n + m + 2) =
      (∑ j ∈ range (n + 1), lucasNumber (j + m)) + lucasNumber (m + 1) := by
  induction n with
  | zero => rw [sum_range_one, zero_add, lucasNumber, add_comm]
  | succ n ih =>
    calc
      lucasNumber (n + 1 + m + 2) =
          lucasNumber (n + m + 2) + lucasNumber (n + 1 + m) := by
        rw [show n + 1 + m + 2 = (n + m + 1) + 2 by omega, lucasNumber,
          show n + m + 1 + 1 = n + m + 2 by omega,
          show n + m + 1 = n + 1 + m by omega]
      _ = _ := by rw [ih, sum_range_succ _ (n + 1)]; ac_rfl

-- Parisse's hyperlucas formula in additive form, so no subtraction of values is needed.
private theorem lucasNumber_shift_eq_hypersequence_add_sum (r n : ℕ) :
    lucasNumber (n + 2 * r) = hypersequence lucasNumber r n +
      ∑ k ∈ range r, (n + k).choose k * lucasNumber (2 * (r - k) - 1) := by
  induction r generalizing n with
  | zero => simp [hypersequence]
  | succ r ih =>
    calc
      lucasNumber (n + 2 * (r + 1)) =
          (∑ j ∈ range (n + 1), lucasNumber (j + 2 * r)) + lucasNumber (2 * r + 1) := by
        rw [show n + 2 * (r + 1) = n + 2 * r + 2 by omega, lucasNumber_add_two_eq_sum]
      _ = hypersequence lucasNumber (r + 1) n +
          ((∑ k ∈ range r, (n + k + 1).choose (k + 1) * lucasNumber (2 * (r - k) - 1)) +
            lucasNumber (2 * r + 1)) := by
        simp_rw [ih]
        rw [sum_add_distrib, ← hypersequence_succ, add_assoc]
        congr 2
        rw [sum_comm]
        simp_rw [← sum_mul, Nat.sum_range_add_choose]
      _ = _ := by
        congr 1
        rw [sum_range_succ']
        simp only [add_zero, Nat.choose_zero_right, one_mul, Nat.sub_zero,
          Nat.add_sub_add_right, ← add_assoc]
        rw [show 2 * (r + 1) - 1 = 2 * r + 1 by omega]

/-- **Lucas numbers as binomial sums.** Let $L_n$ denote the Lucas numbers. For every $r \ge 1$
and every natural number $n$,
$$L_{n+2r} = \sum_{k=0}^{n} \binom{n+r-1-k}{r-1} L_k +
\sum_{k=0}^{r-1} \binom{n+k}{k} L_{2(r-k)-1}$$
and
$$L_{n+2r} = \sum_{k=0}^{n} \binom{r+k-1}{k} L_{n-k} +
\sum_{k=0}^{r-1} \binom{n+k}{k} L_{2(r-k)-1}.$$

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Corollary 2 (`integers-2024-A70-cor-2`). -/
public theorem lucas_add_two_mul_eq_sum_choose {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    lucasNumber (n + 2 * r) =
        ∑ k ∈ range (n + 1), (n + r - 1 - k).choose (r - 1) * lucasNumber k +
          ∑ k ∈ range r, (n + k).choose k * lucasNumber (2 * (r - k) - 1) ∧
      lucasNumber (n + 2 * r) =
        ∑ k ∈ range (n + 1), (r + k - 1).choose k * lucasNumber (n - k) +
          ∑ k ∈ range r, (n + k).choose k * lucasNumber (2 * (r - k) - 1) := by
  have hcast (s m : ℕ) : hypersequence (fun k ↦ (lucasNumber k : ℂ)) s m =
      ((hypersequence lucasNumber s m : ℕ) : ℂ) := by
    induction s generalizing m with
    | zero => rfl
    | succ s ih => simp only [hypersequence_succ, ih, Nat.cast_sum]
  obtain ⟨h₁, h₂⟩ := hypersequence_eq_sum_choose (fun k ↦ (lucasNumber k : ℂ)) hr n
  rw [hcast] at h₁ h₂
  rw [lucasNumber_shift_eq_hypersequence_add_sum]
  constructor
  · congr 1
    exact_mod_cast h₁
  · congr 1
    exact_mod_cast h₂

-- The Fibonacci recurrence telescopes over the positive indices of a shifted prefix.
private theorem fib_add_two_eq_sum (m n : ℕ) :
    Nat.fib (n + m + 2) = Nat.fib (m + 2) + ∑ j ∈ range n, Nat.fib (j + 1 + m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      Nat.fib (n + 1 + m + 2) = Nat.fib (n + m + 2) + Nat.fib (n + 1 + m) := by
        rw [Nat.fib_add_two, show n + 1 + m + 1 = n + m + 2 by omega, add_comm]
      _ = _ := by rw [ih, sum_range_succ, add_assoc]

-- Parisse's hyperfibonacci formula, rearranged to avoid subtracting natural values.
private theorem fib_shift_eq_hypersequence_add_sum (r n : ℕ) :
    Nat.fib (n + 2 * r) = hypersequence Nat.fib r n +
      ∑ k ∈ range r, (n + k - 1).choose k * Nat.fib (2 * (r - k)) := by
  have hzero (s : ℕ) : hypersequence Nat.fib s 0 = 0 := by
    induction s with
    | zero => exact Nat.fib_zero
    | succ s ih => simpa only [hypersequence_succ, Nat.zero_add, sum_range_one] using ih
  have hchoose (n k : ℕ) : ∑ j ∈ range n, (j + k).choose k = (n + k).choose (k + 1) := by
    cases n with
    | zero => rw [sum_range_zero, Nat.zero_add, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self k)]
    | succ n =>
      simpa only [Nat.succ_eq_add_one, Nat.add_right_comm n k 1] using
        Nat.sum_range_add_choose n k
  induction r generalizing n with
  | zero => simp [hypersequence]
  | succ r ih =>
    calc
      Nat.fib (n + 2 * (r + 1)) =
          Nat.fib (2 * r + 2) + ∑ j ∈ range n, Nat.fib (j + 1 + 2 * r) := by
        rw [show n + 2 * (r + 1) = n + 2 * r + 2 by omega, fib_add_two_eq_sum]
      _ = Nat.fib (2 * r + 2) + (hypersequence Nat.fib (r + 1) n +
          ∑ k ∈ range r, (n + k).choose (k + 1) * Nat.fib (2 * (r - k))) := by
        simp_rw [ih, show ∀ j k : ℕ, j + 1 + k - 1 = j + k by omega]
        rw [sum_add_distrib, hypersequence_succ, sum_range_succ', hzero, add_zero]
        congr 2
        rw [sum_comm]
        simp_rw [← sum_mul, hchoose]
      _ = _ := by
        rw [sum_range_succ']
        simp only [Nat.choose_zero_right, one_mul, Nat.sub_zero, Nat.add_sub_add_right,
          show ∀ k : ℕ, n + (k + 1) - 1 = n + k by omega,
          show 2 * (r + 1) = 2 * r + 2 by omega]
        ac_rfl

/-- **Fibonacci numbers as binomially weighted sums.** Let $F_k$ denote the $k$th Fibonacci
number. For every natural number $r \ge 1$ and every natural number $n$,
$$F_{n+2r} = \sum_{k=0}^{n} \binom{n + r - 1 - k}{r - 1} F_k +
\sum_{k=0}^{r-1} \binom{n + k - 1}{k} F_{2(r-k)}$$
and
$$F_{n+2r} = \sum_{k=0}^{n} \binom{r + k - 1}{k} F_{n-k} +
\sum_{k=0}^{r-1} \binom{n + k - 1}{k} F_{2(r-k)}.$$

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Corollary 1 (`integers-2024-A70-cor-1`). -/
public theorem fib_add_two_mul_eq_sum_choose {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    Nat.fib (n + 2 * r) = ∑ k ∈ range (n + 1), (n + r - 1 - k).choose (r - 1) * Nat.fib k +
        ∑ k ∈ range r, (n + k - 1).choose k * Nat.fib (2 * (r - k)) ∧
      Nat.fib (n + 2 * r) = ∑ k ∈ range (n + 1), (r + k - 1).choose k * Nat.fib (n - k) +
        ∑ k ∈ range r, (n + k - 1).choose k * Nat.fib (2 * (r - k)) := by
  have hcast (s m : ℕ) : hypersequence (fun k ↦ (Nat.fib k : ℂ)) s m =
      ((hypersequence Nat.fib s m : ℕ) : ℂ) := by
    induction s generalizing m with
    | zero => rfl
    | succ s ih => simp only [hypersequence_succ, ih, Nat.cast_sum]
  obtain ⟨h₁, h₂⟩ := hypersequence_eq_sum_choose (fun k ↦ (Nat.fib k : ℂ)) hr n
  rw [hcast] at h₁ h₂
  rw [fib_shift_eq_hypersequence_add_sum]
  constructor
  · congr 1
    exact_mod_cast h₁
  · congr 1
    exact_mod_cast h₂

end MetaMathlibExt
