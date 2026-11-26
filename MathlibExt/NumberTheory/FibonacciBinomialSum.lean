/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.KFibonacciTruncatedRecurrence

/-!
# Fibonacci numbers as a truncated binomial sum

The truncation at `k = 2` and the Fibonacci sequence agree from index `2` onward:
they have the same first three values and satisfy the same three-step recurrence.
-/

namespace MetaMathlibExt

private theorem fib_cast_add_three (n : ℕ) :
    (Nat.fib (n + 3) : ℚ) = 2 * (Nat.fib (n + 2) : ℚ) - (Nat.fib n : ℚ) := by
  have h₂ := congrArg (fun m : ℕ => (m : ℚ)) (Nat.fib_add_two (n := n))
  have h₃ := congrArg (fun m : ℕ => (m : ℚ)) (Nat.fib_add_two (n := n + 1))
  simp only [Nat.cast_add] at h₂ h₃
  linear_combination h₃ - h₂

private theorem fib_eq_truncation (n : ℕ) (hn : 2 ≤ n) :
    (Nat.fib n : ℚ) = kFibonacciBinomialTruncation 2 n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases h : 5 ≤ n
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by omega⟩
      rw [kFibonacciBinomialTruncation_recurrence 2 m (by decide) (by omega),
        ← ih (m + 2) (by omega) (by omega), ← ih m (by omega) (by omega)]
      exact fib_cast_add_three m
    · obtain ⟨hsmall, hfour⟩ := kFibonacciBinomialTruncation_initial_values 2 (by decide)
      obtain rfl | rfl | rfl : n = 2 ∨ n = 3 ∨ n = 4 := by omega
      · norm_num [hsmall 2 (by decide) (by decide), Nat.fib_add_two]
      · norm_num [hsmall 3 (by decide) (by decide), Nat.fib_add_two]
      · norm_num [hfour, Nat.fib_add_two]

/-- **Fibonacci numbers as a truncated binomial sum.** Let $F_n$ be the Fibonacci numbers
($F_0 = 0$, $F_1 = 1$, $F_{n+2} = F_{n+1} + F_n$), and for an integer $x$ and a natural number
$j$ let $\binom{x}{j} = x(x-1)\cdots(x-j+1)/j!$. For every natural number $n \ge 2$,
$$
F_n = 2^{n-2} \sum_{\ell=0}^{\lfloor (n-1)/3 \rfloor}
\left(\binom{3\ell - n}{\ell} - \binom{3\ell - n}{\ell - 1}\right) 2^{-3\ell},
$$
where the term $\binom{3\ell - n}{\ell - 1}$ is taken to be $0$ for $\ell = 0$.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1,
Corollary 13 (`jis-2024-24.1.1-cor-13`). -/
public theorem fib_eq_binomial_sum (n : ℕ) (hn : 2 ≤ n) :
    (Nat.fib n : ℚ) = 2 ^ (n - 2) * ∑ ℓ ∈ Finset.range ((n - 1) / 3 + 1),
      ((Ring.choose ((3 * ℓ : ℕ) - (n : ℤ)) ℓ -
        (if ℓ = 0 then 0 else Ring.choose ((3 * ℓ : ℕ) - (n : ℤ)) (ℓ - 1)) : ℤ) : ℚ) /
        2 ^ (3 * ℓ) := by
  have hexp : (n : ℤ) - 2 = ((n - 2 : ℕ) : ℤ) := by omega
  rw [fib_eq_truncation n hn, kFibonacciBinomialTruncation, hexp, zpow_natCast]

end MetaMathlibExt
