/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Fibonacci and Lucas polynomial identities for super FiboCatalan numbers

This module proves the Fibonacci and Lucas cross-product identities and uses the Lucas identity
to relate consecutive Lucas Catalan numbers after clearing denominators.
-/

public section

namespace MathlibExt.NumberTheory.SuperFibocatalanWanted

/-- **Fibonacci identity $F_{2n} F_{n+2} - F_{2n+2} F_n = (-1)^n F_n$.** For every natural
number $n$, the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$, $F_{k+2} = F_{k+1} + F_k$) satisfy
$F_{2n} F_{n+2} - F_{2n+2} F_n = (-1)^n F_n$.

Source: Kendra Killpatrick, "Super FiboCatalan Numbers and
Their Lucas Analogues", Lemma 6. -/
theorem fib_mul_sub_mul (n : ℕ) :
    (Nat.fib (2 * n) : ℤ) * (Nat.fib (n + 2) : ℤ) -
        (Nat.fib (2 * n + 2) : ℤ) * (Nat.fib n : ℤ) =
      (-1) ^ n * (Nat.fib n : ℤ) := by
  -- Shifting both pairs of consecutive indices by one negates their determinant.
  have shift (k : ℕ) :
      (Nat.fib (n + k) : ℤ) * Nat.fib (k + 1) - (Nat.fib (n + k + 1) : ℤ) * Nat.fib k =
        (-1) ^ k * (Nat.fib n : ℤ) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.add_succ n k, pow_succ, Nat.fib_add_two (n := k), Nat.fib_add_two (n := n + k)]
      push_cast
      linear_combination -ih
  rw [two_mul, Nat.fib_add_two (n := n), Nat.fib_add_two (n := n + n)]
  push_cast
  linear_combination shift n

/-- **Lucas polynomials in $s$ and $t$.** The Lucas polynomials $\{n\}$, for natural numbers
$n$, are the polynomials in two variables $s$ and $t$ with integer coefficients defined by
$\{0\} = 0$, $\{1\} = 1$ and $\{n + 2\} = s\{n + 1\} + t\{n\}$ for every $n \ge 0$. -/
@[expose] noncomputable def lucasPoly : ℕ → MvPolynomial (Fin 2) ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => MvPolynomial.X 0 * lucasPoly (n + 1) +
      MvPolynomial.X 1 * lucasPoly n

open MvPolynomial in
/-- **Cross-product identity for Lucas polynomials.** For every natural number $n$, the Lucas
polynomials $\{k\}$ in $s$ and $t$ satisfy
$\{2n\}\{n + 2\} - \{2n + 2\}\{n\} = (-1)^n \{2\} t^n \{n\}$.

Source: Kendra Killpatrick, "Super FiboCatalan Numbers and
Their Lucas Analogues", Lemma 10. -/
theorem lucasPoly_mul_sub_mul (n : ℕ) :
    lucasPoly (2 * n) * lucasPoly (n + 2) -
        lucasPoly (2 * n + 2) * lucasPoly n =
      (-1) ^ n * lucasPoly 2 * MvPolynomial.X 1 ^ n * lucasPoly n := by
  -- Shifting both pairs of indices by one multiplies their determinant by -t.
  have shift (k : ℕ) :
      lucasPoly (n + k) * lucasPoly (k + 1) - lucasPoly (n + k + 1) * lucasPoly k =
        (-1) ^ k * X 1 ^ k * lucasPoly n := by
    induction k with
    | zero => simp [lucasPoly]
    | succ k ih =>
      rw [Nat.add_succ n k]
      simp only [lucasPoly, pow_succ]
      linear_combination -(X 1) * ih
  simp only [two_mul, lucasPoly, mul_one, mul_zero, add_zero]
  linear_combination X 0 * shift n

/-- **Lucas factorial.** For a natural number $n$, the Lucas factorial $\{n\}!$ is the product
$\{n\}! = \{1\}\{2\} \cdots \{n\}$ of the Lucas polynomials $\{i\}$ in $s$ and $t$ for
$1 \le i \le n$, a polynomial with integer coefficients; in particular $\{0\}! = 1$, the empty
product. -/
@[expose] noncomputable def lucasFactorial (n : ℕ) : MvPolynomial (Fin 2) ℤ :=
  ∏ i ∈ Finset.Icc 1 n, lucasPoly i

/-- **Lucas analogue of the FiboCatalan identity, cleared of denominators.** Let $\{k\}$ be
the Lucas polynomials in $s$ and $t$ ($\{0\} = 0$, $\{1\} = 1$, $\{k+2\} = s\{k+1\} + t\{k\}$)
and let $\{k\}! = \{1\}\{2\} \cdots \{k\}$ be the Lucas factorial. For every natural number
$n$, in $\mathbb{Z}[s, t]$,
$$(\{2n+1\} \{2n\} \{n+2\} - \{2n+2\} \{2n+1\} \{n\}) \, \{2n\}!
= (-1)^n t^n \{2\} \{n\} \{2n+1\} \, \{2n\}!.$$

With the Lucas Catalan numbers $C_{\{k\}} = \{2k\}!/(\{k\}! \, \{k+1\}!)$, this is the identity
$$\{2n+1\} \{2n\} C_{\{n\}} - \{n+1\} \{n\} C_{\{n+1\}}
= (-1)^n t^n \{2\} \{n\} \{2n+1\} \frac{\{2n\}!}{\{n+2\}! \, \{n\}!}$$
multiplied through by $\{n+2\}! \, \{n\}!$.

Source: Kendra Killpatrick, "Super FiboCatalan Numbers and
Their Lucas Analogues", Theorem 11. -/
theorem lucasCatalan_identity_mul_factorial (n : ℕ) :
    (lucasPoly (2 * n + 1) * lucasPoly (2 * n) * lucasPoly (n + 2) -
        lucasPoly (2 * n + 2) * lucasPoly (2 * n + 1) *
          lucasPoly n) * lucasFactorial (2 * n) =
      (-1) ^ n * MvPolynomial.X 1 ^ n * lucasPoly 2 *
        lucasPoly n * lucasPoly (2 * n + 1) *
        lucasFactorial (2 * n) := by
  linear_combination lucasPoly (2 * n + 1) * lucasFactorial (2 * n) * lucasPoly_mul_sub_mul n

end MathlibExt.NumberTheory.SuperFibocatalanWanted
