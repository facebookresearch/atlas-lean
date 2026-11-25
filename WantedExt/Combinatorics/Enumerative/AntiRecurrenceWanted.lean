/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.ModEq
public import MathlibExt.Combinatorics.Enumerative.AntiRecurrenceGaps
public import MathlibExt.Combinatorics.Words.Automatic
public import WantedExt.Combinatorics.Enumerative.WalnutOeisProblemsWanted

/-!
# Anti-recurrence sequences

Statements from Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26
(2026), Article A24. A positive linear form `a = (a_1, …, a_k)` with `k > 1` generates a pair of
complementary sequences: the non-anti-recurrence numbers `B_1 < B_2 < ⋯` are produced block by
block by the mex rule, and the anti-recurrence numbers are
`A_n = ∑_j a_j B_{(n-1)k + j}`. The trace is `τ = ∑_j a_j`, and `κ = kτ + 1`.

The linear form is a list `a`, so `k = a.length` and `τ = a.sum`. The construction uses the
positive mex `antiTribonacciMex`. For `a = [1, 1]` and `a = [1, 1, 1]` it gives the anti-Fibonacci
and anti-Tribonacci numbers `antiFibonacciC` and `antiTribonacciD` of `WalnutOeisProblemsWanted`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **First anti-Fibonacci anti-recurrence numbers.** The anti-recurrence numbers
$A_1, A_2, A_3, A_4$ of the linear form $(1, 1)$ are $3, 9, 13, 18$, and the first four
anti-Fibonacci numbers $C_1, C_2, C_3, C_4$ of the Walnut anti-Fibonacci construction
(OEIS A075326) are also $3, 9, 13, 18$; so the two sequences agree for $1 \le n \le 4$.

Source: Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026),
Article A24, Section 1. -/
theorem antiRecurrence_antiFibonacci_small :
    (List.range 4).map (fun n => antiRecurrence [1, 1] (n + 1)) = [3, 9, 13, 18] ∧
      (List.range 4).map (fun n => antiFibonacciC (n + 1)) = [3, 9, 13, 18] := by
  decide +kernel

/-- **First anti-Pell numbers.** The anti-recurrence numbers $A_1, A_2, A_3, A_4$ of the linear
form $(1, 2)$, the anti-Pell numbers (OEIS A304502), are $5, 11, 20, 26$, and its first eight
non-anti-recurrence numbers $B_1, \dots, B_8$ are $1, 2, 3, 4, 6, 7, 8, 9$ (so
$B^1_n = B_{2n-1}$ starts $1, 3, 6, 8$ and $B^2_n = B_{2n}$ starts $2, 4, 7, 9$).

Source: Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026),
Article A24, Section 3. -/
theorem antiRecurrence_antiPell_small :
    (List.range 4).map (fun n => antiRecurrence [1, 2] (n + 1)) = [5, 11, 20, 26] ∧
      (List.range 8).map (fun m => antiRecurrenceComplement [1, 2] (m + 1)) =
        [1, 2, 3, 4, 6, 7, 8, 9] := by
  decide +kernel

/-- **First anti-Jacobsthal numbers.** The anti-recurrence numbers $A_1, A_2, A_3, A_4$ of the
linear form $(2, 1)$, the anti-Jacobsthal numbers (OEIS A304499), are $4, 11, 19, 25$.

Source: Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026),
Article A24, Section 3. -/
theorem antiRecurrence_antiJacobsthal_small :
    (List.range 4).map (fun n => antiRecurrence [2, 1] (n + 1)) = [4, 11, 19, 25] := by
  decide +kernel

/-- **First anti-Tribonacci anti-recurrence numbers.** The anti-recurrence numbers
$A_1, A_2, A_3, A_4$ of the linear form $(1, 1, 1)$ are $6, 16, 27, 36$, and the first four
anti-Tribonacci numbers $D_1, D_2, D_3, D_4$ of the Walnut anti-Tribonacci construction
(OEIS A265389) are also $6, 16, 27, 36$; so the two sequences agree for $1 \le n \le 4$.

Source: Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026),
Article A24, Section 4. -/
theorem antiRecurrence_antiTribonacci_small :
    (List.range 4).map (fun n => antiRecurrence [1, 1, 1] (n + 1)) = [6, 16, 27, 36] ∧
      (List.range 4).map (fun n => antiTribonacciD (n + 1)) = [6, 16, 27, 36] := by
  decide +kernel

/-- **Characterization of anti-recurrence sequences.** Let $a = (a_1, \dots, a_k)$ be a linear
form with positive integer coefficients and $k > 1$, with anti-recurrence numbers
$A_1, A_2, \dots$ and non-anti-recurrence numbers $B_1, B_2, \dots$. Let $(x_i)_{i \ge 0}$ and
$(y_i)_{i \ge 0}$ be sequences of natural numbers. Then $x$ and $y$ are strictly increasing, every
$y_i$ is positive, every positive integer is a term of exactly one of $x$ and $y$, and
$x_i = \sum_{j=1}^{k} a_j y_{ik+j-1}$ for all $i$, if and only if $x_i = A_{i+1}$ and
$y_i = B_{i+1}$ for all $i$.

Source: Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026),
Article A24, Lemma 2 (`integers-2026-A24-lem-2`). -/
public theorem_wanted antiRecurrence_unique (a : List ℕ) (ha : ∀ x ∈ a, 0 < x)
    (hk : 1 < a.length) (A B : ℕ → ℕ) :
    (StrictMono A ∧ StrictMono B ∧ (∀ i, 0 < B i) ∧
        (∀ m, 0 < m → (m ∈ Set.range A ↔ m ∉ Set.range B)) ∧
        ∀ i, A i = ∑ j : Fin a.length, a[j] * B (i * a.length + j)) ↔
      (A = fun i => antiRecurrence a (i + 1)) ∧ B = fun i => antiRecurrenceComplement a (i + 1)

/-- **Interval location of anti-recurrence numbers for bounded forms.** Let
$a = (a_1, \dots, a_k)$ be a linear form with positive integer coefficients and $k > 1$, of trace
$\tau = a_1 + \dots + a_k$, with anti-recurrence numbers $A_1, A_2, \dots$ and non-anti-recurrence
numbers $B_1, B_2, \dots$, and let $\kappa = k\tau + 1$. Suppose that $a$ is $A_1$-bounded, that
is, $A_1 \le (k - 1)\tau + 2$. Then for every $n \ge 1$, $A_n$ lies in the interval
$I_n = [\kappa(n - 1) + 1, \kappa n]$, and the first $k$ numbers of $I_n$ are non-anti-recurrence
numbers: $B_{(n-1)k\tau + j} = \kappa(n - 1) + j$ for $1 \le j \le k$.

Source: Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026),
Article A24, Lemma 5 (`integers-2026-A24-lem-5`). -/
public theorem_wanted antiRecurrence_mem_Icc_of_bounded (a : List ℕ) (ha : ∀ x ∈ a, 0 < x)
    (hk : 1 < a.length) (hb : antiRecurrence a 1 ≤ (a.length - 1) * a.sum + 2) {n : ℕ}
    (hn : 1 ≤ n) :
    antiRecurrence a n ∈
        Finset.Icc ((a.length * a.sum + 1) * (n - 1) + 1) ((a.length * a.sum + 1) * n) ∧
      ∀ j < a.length, antiRecurrenceComplement a ((n - 1) * a.length * a.sum + j + 1) =
        (a.length * a.sum + 1) * (n - 1) + j + 1

/-- **Kimberling's bounds for the anti-Pell numbers.** Let $A_n$ be the anti-recurrence numbers
of the linear form $a = (1, 2)$ (the anti-Pell numbers), let $B_m$ be its non-anti-recurrence
numbers, and put $B^1_n = B_{2n-1}$ and $B^2_n = B_{2n}$. Then for every $n \ge 1$ we have
$0 \le A_n - 7n + 3 \le 2$, $0 \le 3B^1_n - 7n + 6 \le 3$ and $0 \le 3B^2_n - 7n + 2 \le 3$.

Source: Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026),
Article A24, Theorem 1 (`integers-2026-A24-thm-1`). -/
public theorem_wanted antiPell_kimberling_bounds {n : ℕ} (hn : 1 ≤ n) :
    (0 ≤ (antiRecurrence [1, 2] n : ℤ) - 7 * n + 3 ∧
        (antiRecurrence [1, 2] n : ℤ) - 7 * n + 3 ≤ 2) ∧
      (0 ≤ 3 * (antiRecurrenceComplement [1, 2] (2 * n - 1) : ℤ) - 7 * n + 6 ∧
        3 * (antiRecurrenceComplement [1, 2] (2 * n - 1) : ℤ) - 7 * n + 6 ≤ 3) ∧
      (0 ≤ 3 * (antiRecurrenceComplement [1, 2] (2 * n) : ℤ) - 7 * n + 2 ∧
        3 * (antiRecurrenceComplement [1, 2] (2 * n) : ℤ) - 7 * n + 2 ≤ 3)

/-- **Kimberling's bounds for the anti-Jacobsthal numbers.** Let $A_n$ be the anti-recurrence
numbers of the linear form $a = (2, 1)$ (the anti-Jacobsthal numbers), let $B_m$ be its
non-anti-recurrence numbers, and put $B^1_n = B_{2n-1}$ and $B^2_n = B_{2n}$. Then for every
$n \ge 1$ we have $0 \le A_n - 7n + 4 \le 3$, $0 \le 3B^1_n - 7n + 6 \le 4$ and
$0 \le 3B^2_n - 7n + 2 \le 3$.

Source: Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026),
Article A24, Theorem 2 (`integers-2026-A24-thm-2`). -/
public theorem_wanted antiJacobsthal_kimberling_bounds {n : ℕ} (hn : 1 ≤ n) :
    (0 ≤ (antiRecurrence [2, 1] n : ℤ) - 7 * n + 4 ∧
        (antiRecurrence [2, 1] n : ℤ) - 7 * n + 4 ≤ 3) ∧
      (0 ≤ 3 * (antiRecurrenceComplement [2, 1] (2 * n - 1) : ℤ) - 7 * n + 6 ∧
        3 * (antiRecurrenceComplement [2, 1] (2 * n - 1) : ℤ) - 7 * n + 6 ≤ 4) ∧
      (0 ≤ 3 * (antiRecurrenceComplement [2, 1] (2 * n) : ℤ) - 7 * n + 2 ∧
        3 * (antiRecurrenceComplement [2, 1] (2 * n) : ℤ) - 7 * n + 2 ≤ 3)

/-- **Bounded anti-recurrence sequences are automatic up to a linear term.** Let
$a = (a_1, \dots, a_k)$ be a linear form with positive integer coefficients and $k > 1$, of trace
$\tau = a_1 + \dots + a_k$, with anti-recurrence numbers $A_1, A_2, \dots$, and let
$\kappa = k\tau + 1$. If $a$ is $A_1$-bounded, that is, $A_1 \le (k - 1)\tau + 2$, then the
integer sequence $n \mapsto A_{n+1} - \kappa(n + 1)$, indexed from $n = 0$, is $\tau$-automatic:
$\tau \ge 2$ and its $\tau$-kernel is finite.

Automaticity is stated through Eilenberg's characterization by a finite kernel, in place of the
paper's definition by a finite automaton with output.

Source: Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026),
Article A24, Theorem 4 (`integers-2026-A24-thm-4`). -/
public theorem_wanted antiRecurrence_sub_isKAutomatic_of_bounded (a : List ℕ)
    (ha : ∀ x ∈ a, 0 < x) (hk : 1 < a.length)
    (hb : antiRecurrence a 1 ≤ (a.length - 1) * a.sum + 2) :
    IsKAutomatic a.sum fun n =>
      (antiRecurrence a (n + 1) : ℤ) - (a.length * a.sum + 1) * (n + 1)

end

end MetaMathlibExt
