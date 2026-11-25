/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Gutkovskiy's sequence -/

namespace MetaMathlibExt

@[expose] public section

/-- **Table of Gutkovskiy's sequence.** The Gutkovskiy tables $T_0, T_1, \dots$ are finite lists
of natural numbers, indexed from $0$, defined by $T_0 = [0]$ and, for $n \ge 0$, $T_{n+1}$ is
$T_n$ with the entry $(n + 1) - T_n[\lfloor T_n[n]/2 \rfloor]$ appended at the end. Here $T_n[j]$
is the entry of $T_n$ at index $j$, or $0$ if $T_n$ has fewer than $j + 1$ entries, and the
subtraction is truncated at $0$.

$T_n$ has $n + 1$ entries and lists the terms $g_0, \dots, g_n$ of Gutkovskiy's sequence, so each
step reads only values already computed.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public def gutkovskiyTable : ℕ → Array ℕ
  | 0 => #[0]
  | n + 1 =>
    let a := gutkovskiyTable n
    a.push ((n + 1) - a.getD (a.getD n 0 / 2) 0)

/-- **Gutkovskiy's sequence.** Gutkovskiy's sequence (OEIS A286389) is the sequence of natural
numbers $g_0, g_1, \dots$ with $g_0 = 0$ and $g_n = n - g_{\lfloor g_{n-1}/2 \rfloor}$ for
$n \ge 1$ (subtraction of natural numbers, truncated at $0$).

Formally, $g_n$ is defined as $T_n[n]$, the entry at index $n$ of the Gutkovskiy table $T_n$, and
the recurrence is proved from the table.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public def gutkovskiy (n : ℕ) : ℕ :=
  (gutkovskiyTable n).getD n 0

/-- **Number of entries of the Gutkovskiy table.** For every natural number $n$, the Gutkovskiy
table up to index $n$, the array of the values $g_0, \dots, g_n$ of Gutkovskiy's sequence, has
exactly $n + 1$ entries.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public theorem size_gutkovskiyTable (n : ℕ) : (gutkovskiyTable n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [gutkovskiyTable, ih]

/-- **Entries of the Gutkovskiy table.** For natural numbers $k \le n$, the entry at index $k$
(counting from $0$) of the Gutkovskiy table $T_n$ is the term $g_k$ of Gutkovskiy's sequence.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public theorem getD_gutkovskiyTable {k n : ℕ} (h : k ≤ n) :
    (gutkovskiyTable n).getD k 0 = gutkovskiy k := by
  induction n with
  | zero => obtain rfl : k = 0 := by omega
            rfl
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · rw [← ih (by omega)]
      simp only [gutkovskiyTable, Array.getD_eq_getD_getElem?, Array.getElem?_push,
        size_gutkovskiyTable]
      simp [show k ≠ n + 1 by omega]
    · obtain rfl : k = n + 1 := by omega
      rfl

/-- **Gutkovskiy's sequence is bounded by the index.** For every natural number $n$, the term
$g_n$ of Gutkovskiy's sequence satisfies $g_n \le n$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public theorem gutkovskiy_le (n : ℕ) : gutkovskiy n ≤ n := by
  cases n with
  | zero => decide
  | succ n =>
    have : gutkovskiy (n + 1) = (n + 1) - (gutkovskiyTable n).getD
        ((gutkovskiyTable n).getD n 0 / 2) 0 := by
      simp only [gutkovskiy, gutkovskiyTable, Array.getD_eq_getD_getElem?, Array.getElem?_push,
        size_gutkovskiyTable, ↓reduceIte, Option.getD_some]
    omega

/-- **Recurrence for Gutkovskiy's sequence.** For every natural number $n$, Gutkovskiy's sequence
satisfies $g_{n+1} = (n + 1) - g_{\lfloor g_n/2 \rfloor}$ (subtraction of natural numbers,
truncated at $0$).

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public theorem gutkovskiy_succ (n : ℕ) :
    gutkovskiy (n + 1) = (n + 1) - gutkovskiy (gutkovskiy n / 2) := by
  have h1 : gutkovskiy (n + 1) = (n + 1) - (gutkovskiyTable n).getD
      ((gutkovskiyTable n).getD n 0 / 2) 0 := by
    simp only [gutkovskiy, gutkovskiyTable, Array.getD_eq_getD_getElem?, Array.getElem?_push,
      size_gutkovskiyTable, ↓reduceIte, Option.getD_some]
  rw [h1, getD_gutkovskiyTable le_rfl, getD_gutkovskiyTable
    (le_trans (Nat.div_le_self _ _) (gutkovskiy_le n))]

/-- **First terms of Gutkovskiy's sequence.** The first four terms of Gutkovskiy's sequence are
$g_0 = 0$, $g_1 = 1$, $g_2 = 2$ and $g_3 = 2$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Table 1. -/
public theorem gutkovskiy_initial :
    gutkovskiy 0 = 0 ∧ gutkovskiy 1 = 1 ∧ gutkovskiy 2 = 2 ∧ gutkovskiy 3 = 2 := by
  have h0 : gutkovskiy 0 = 0 := rfl
  have h1 : gutkovskiy 1 = 1 := by rw [gutkovskiy_succ, h0, h0]
  have h2 : gutkovskiy 2 = 2 := by rw [gutkovskiy_succ, h1, h0]
  have h3 : gutkovskiy 3 = 2 := by rw [gutkovskiy_succ, h2, h1]
  exact ⟨h0, h1, h2, h3⟩

/-- **Gutkovskiy's sequence at $100$.** The term $g_{100}$ of Gutkovskiy's sequence is $74$, in
agreement with OEIS A286389.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public theorem gutkovskiy_hundred : gutkovskiy 100 = 74 := by
  decide +kernel

end

private theorem gutkovskiy_step (n : ℕ) :
    gutkovskiy n ≤ gutkovskiy (n + 1) ∧ gutkovskiy (n + 1) ≤ gutkovskiy n + 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [gutkovskiy_initial.1, gutkovskiy_initial.2.1]
    | succ n =>
      have hprev := ih n (by omega)
      let i := gutkovskiy n / 2
      let j := gutkovskiy (n + 1) / 2
      have hij : i ≤ j ∧ j ≤ i + 1 := by dsimp [i, j]; omega
      have hi : i ≤ n := (Nat.div_le_self _ _).trans (gutkovskiy_le n)
      have hj : j ≤ n + 1 := (Nat.div_le_self _ _).trans (gutkovskiy_le (n + 1))
      have hgi := (gutkovskiy_le i).trans hi
      have hgj := (gutkovskiy_le j).trans hj
      have h₁ : gutkovskiy (n + 1) = n + 1 - gutkovskiy i := gutkovskiy_succ n
      have h₂ : gutkovskiy (n + 2) = n + 2 - gutkovskiy j := gutkovskiy_succ (n + 1)
      -- The two successive recurrence calls either read the same term or adjacent terms.
      by_cases heq : i = j
      · rw [← heq] at h₂
        change gutkovskiy (n + 1) ≤ gutkovskiy (n + 2) ∧
          gutkovskiy (n + 2) ≤ gutkovskiy (n + 1) + 1
        omega
      · have hnext : j = i + 1 := by omega
        have hgap := ih i (by omega)
        rw [hnext] at h₂
        change gutkovskiy (n + 1) ≤ gutkovskiy (n + 2) ∧
          gutkovskiy (n + 2) ≤ gutkovskiy (n + 1) + 1
        omega

private theorem gutkovskiy_half_succ (n : ℕ) :
    gutkovskiy (n + 1) / 2 = gutkovskiy n / 2 + gutkovskiy n % 2 := by
  have hstep := gutkovskiy_step n
  by_cases heven : gutkovskiy n % 2 = 0
  · omega
  · have hinc : gutkovskiy (n + 1) = gutkovskiy n + 1 := by
      cases n with
      | zero => exact (heven (by decide)).elim
      | succ k =>
        have hprev := gutkovskiy_step k
        -- An odd term and its predecessor have the same half, so the next step is one.
        have hsame : gutkovskiy (k + 1) / 2 = gutkovskiy k / 2 := by omega
        have h₁ := gutkovskiy_succ k
        have h₂ : gutkovskiy (k + 2) = k + 2 - gutkovskiy (gutkovskiy (k + 1) / 2) :=
          gutkovskiy_succ (k + 1)
        have hbound := (gutkovskiy_le (gutkovskiy k / 2)).trans
          ((Nat.div_le_self _ _).trans (gutkovskiy_le k))
        change gutkovskiy (k + 2) = gutkovskiy (k + 1) + 1
        rw [h₂, hsame, h₁]
        omega
    omega

/-- **Gutkovskiy's sequence from its parities.** Let $g_0, g_1, \dots$ be Gutkovskiy's sequence,
let $g'_n = g_n \bmod 2$ and let $h_n = \sum_{0 \le i < n} g'_i$. Then $g_n = 2h_n + g'_n$ for
every $n \ge 0$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 5 (`integers-2024-A51-thm-5`). -/
public theorem gutkovskiy_eq_two_mul_sum_mod_two_add (n : ℕ) :
    gutkovskiy n = 2 * ∑ i ∈ Finset.range n, gutkovskiy i % 2 + gutkovskiy n % 2 := by
  have hhalf (k : ℕ) : gutkovskiy k / 2 = ∑ i ∈ Finset.range k, gutkovskiy i % 2 := by
    induction k with
    | zero => simp [gutkovskiy_initial.1]
    | succ k ih => rw [gutkovskiy_half_succ, ih, Finset.sum_range_succ]
  have h := hhalf n
  omega

end MetaMathlibExt
