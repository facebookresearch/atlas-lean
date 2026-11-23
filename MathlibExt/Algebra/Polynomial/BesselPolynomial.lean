/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Tactic.NormNum

/-!
# Bessel polynomials (classical definition)

Formalizes the classical n-th Bessel polynomial from the Schork source
(lines 285-288), concept `jis_sem_0d5596f0982681bcb579a894`.
-/

namespace MetaMathlibExt

open scoped BigOperators

@[expose] public section

/-- **Bessel polynomial.** For a natural number $n$, the $n$-th classical Bessel polynomial
$y_n$ is the polynomial with rational coefficients
$y_n(x) = \sum_{k=0}^{n} \frac{(n+k)!}{2^k \, k! \, (n-k)!} \, x^k$.

Source: Schork, lines 285-288 (concept `jis_sem_0d5596f0982681bcb579a894`). -/
noncomputable def besselPolynomial (n : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C ((Nat.factorial (n + k) : ℚ) /
      ((2 ^ k : ℚ) * (Nat.factorial k : ℚ) * (Nat.factorial (n - k) : ℚ))) *
      (Polynomial.X ^ k)

/-- **Explicit formula for the Bessel polynomials.** For every natural number $n$, the Bessel
polynomial $y_n \in \mathbb{Q}[x]$ equals
$\sum_{k=0}^{n} \frac{(n+k)!}{2^k \, k! \, (n-k)!} \, x^k$.

This is the defining formula, so the identity holds by definition.

Source: Schork, lines 285-288 (concept `jis_sem_0d5596f0982681bcb579a894`). -/
theorem besselPolynomial_eq_sum (n : ℕ) :
    besselPolynomial n =
      ∑ k ∈ Finset.range (n + 1),
        Polynomial.C ((Nat.factorial (n + k) : ℚ) /
          ((2 ^ k : ℚ) * (Nat.factorial k : ℚ) * (Nat.factorial (n - k) : ℚ))) *
          (Polynomial.X ^ k) :=
  rfl

/-- **The zeroth Bessel polynomial.** The Bessel polynomial $y_0$ is the constant
polynomial $1$.

Source: Schork, lines 285-288 (concept `jis_sem_0d5596f0982681bcb579a894`). -/
theorem besselPolynomial_zero : besselPolynomial 0 = 1 := by
  unfold besselPolynomial
  norm_num [Finset.sum_range_one]

/-- **The first Bessel polynomial.** The Bessel polynomial $y_1$ equals $1 + x$.

Source: Schork, lines 285-288 (concept `jis_sem_0d5596f0982681bcb579a894`). -/
theorem besselPolynomial_one :
    besselPolynomial 1 = Polynomial.C 1 + Polynomial.X := by
  unfold besselPolynomial
  norm_num [Finset.sum_range_succ, Finset.sum_range_one]

/-- **The second Bessel polynomial.** The Bessel polynomial $y_2$ equals $1 + 3x + 3x^2$.

Source: Schork, lines 285-288 (concept `jis_sem_0d5596f0982681bcb579a894`). -/
theorem besselPolynomial_two :
    besselPolynomial 2 =
      Polynomial.C 1 + Polynomial.C 3 * Polynomial.X +
        Polynomial.C 3 * (Polynomial.X ^ 2) := by
  unfold besselPolynomial
  simp only [Finset.sum_range_succ]
  norm_num [Nat.factorial]

end

end MetaMathlibExt
