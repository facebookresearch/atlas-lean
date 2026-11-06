/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Generalizations of several explicit formulas for Euler polynomials

Statements from Nouara Mokhtari, Rachid Boumahdi, and
Farid Bencherif, "Generalizations of Several Explicit
Formulas for Euler Polynomials", *INTEGERS* 25 (2025),
Article A65
(<https://math.colgate.edu/~integers/vol25.html>).

The Euler polynomial `E_n(x)` is `eulerPoly n`, defined
through Bernoulli polynomials by
`E_n(x) = (2 / (n + 1)) (B_{n+1}(x) - 2^{n+1} B_{n+1}(x / 2))`.
The paper's generalized Stirling polynomial
`S(n, k, x) = (1 / k!) ∑_j (k choose j) (-1)^{k-j} (x + j)^n`
(Proposition 3.1) is `genStirlingPoly n k`. The
coefficients `α_k` of the paper's Lemma 2.2, the Taylor
coefficients of `(2 + 2z) / (2 + 2z + z^2)`, are
`eulerAlpha`, defined by the recurrence that generating
function imposes. The order-`α` Euler polynomials
`E_n^{(α)}(x)` (with generating function
`(2 / (e^t + 1))^α e^{xt}`) are `eulerPolyGen`, built
from the numbers `eulerNumGen α k = E_k^{(α)}(0)`, which
are defined by the coefficient recurrence of that
generating function's logarithmic derivative. All
formulas below were pinned and verified by exact rational
computation (the extraction of this paper flattens most
displays; the ranges and coefficients stated here are the
unique readings consistent with the surviving fragments).

Not stated (see the source audit table): Lemmas 2.1, 2.3
and 2.4 (statements inside the paper's operator/Appell
framework), Lemma 2.2's closed form for `α_k` (its
summand is not recoverable from the extraction; `α_k` is
instead pinned by the generating function), and
Theorem 4.4 (its formula could not be recovered).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

@[expose] public section

open Polynomial

namespace MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

/-- **Euler polynomials.** Let $B_m(x)$ denote the $m$-th Bernoulli polynomial. For $n \ge 0$,
the Euler polynomial $E_n(x)$ is the polynomial with rational coefficients
$E_n(x) = \frac{2}{n + 1} \left(B_{n+1}(x) - 2^{n+1} B_{n+1}(x/2)\right)$.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Section 1 (Euler polynomials). -/
noncomputable def eulerPoly (n : ℕ) : ℚ[X] :=
  (2 / (n + 1 : ℚ)) • (Polynomial.bernoulli (n + 1) -
    (2 : ℚ) ^ (n + 1) •
      (Polynomial.bernoulli (n + 1)).comp (C (1 / 2) * X))

/-- **Generalized Stirling polynomial.** For natural numbers $n$ and $k$, the generalized
Stirling polynomial $S(n, k, x)$ is the polynomial in $x$ with rational coefficients
$$S(n, k, x) = \frac{1}{k!} \sum_{j=0}^{k} \binom{k}{j} (-1)^{k-j} (x + j)^n.$$

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Proposition 3.1 (definition). -/
noncomputable def genStirlingPoly (n k : ℕ) : ℚ[X] :=
  (1 / (Nat.factorial k : ℚ)) •
    ∑ j ∈ Finset.range (k + 1),
      ((Nat.choose k j : ℚ) * (-1) ^ (k - j)) •
        (X + C (j : ℚ)) ^ n

/-- **Taylor coefficients of (2 + 2z)/(2 + 2z + z²).** The rational numbers $\alpha_k$,
$k \ge 0$, are defined by $\alpha_0 = 1$, $\alpha_1 = 0$ and
$2\alpha_{k+2} + 2\alpha_{k+1} + \alpha_k = 0$ for every $k \ge 0$. They are the Taylor
coefficients of $(2 + 2z)/(2 + 2z + z^2)$ at $z = 0$.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Lemma 2.2 (generating function). -/
def eulerAlpha : ℕ → ℚ
  | 0 => 1
  | 1 => 0
  | k + 2 => -eulerAlpha (k + 1) - eulerAlpha k / 2

/-- **Fuel-bounded recurrence for the Euler numbers of order α.** Let $E_m(x)$ denote the Euler
polynomial. For a complex number $\alpha$, the complex numbers $a_\alpha(f, n)$, for natural
numbers $f$ (the fuel) and $n$, are defined by $a_\alpha(0, n) = 1$, $a_\alpha(f + 1, 0) = 1$
and $a_\alpha(f + 1, n + 1) = -\alpha \, a_\alpha(f, n) +
\frac{\alpha}{2} \sum_{k=0}^{n} \binom{n}{k} a_\alpha(f, k) \, E_{n-k}(0)$.

Whenever $n \le f$, $a_\alpha(f, n)$ equals the Euler number of order $\alpha$,
$E_n^{(\alpha)}(0)$. -/
noncomputable def eulerNumGenAux (α : ℂ) : ℕ → ℕ → ℂ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | fuel + 1, n + 1 =>
      -α * eulerNumGenAux α fuel n + (α / 2) *
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℂ) * eulerNumGenAux α fuel k *
            (((eulerPoly (n - k)).eval (0 : ℚ) : ℚ) : ℂ)

/-- **Euler numbers of order α.** Let $E_m(x)$ denote the Euler polynomial. For a complex number
$\alpha$, the Euler numbers of order $\alpha$ are the complex numbers $E_n^{(\alpha)}(0)$,
$n \ge 0$, defined by $E_0^{(\alpha)}(0) = 1$ and
$E_{n+1}^{(\alpha)}(0) = -\alpha E_n^{(\alpha)}(0) +
\frac{\alpha}{2} \sum_{k=0}^{n} \binom{n}{k} E_k^{(\alpha)}(0) \, E_{n-k}(0)$ for $n \ge 0$.

This is the coefficient recurrence of the generating function $(2/(e^t + 1))^\alpha$.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Section 1 (generalized Euler
polynomials). -/
noncomputable def eulerNumGen (α : ℂ) (n : ℕ) : ℂ :=
  eulerNumGenAux α n n

/-- **Euler polynomials of order α.** For a complex number $\alpha$ and $n \ge 0$, let
$E_k^{(\alpha)}(0)$ denote the Euler numbers of order $\alpha$. The Euler polynomial of order
$\alpha$ is the complex polynomial
$E_n^{(\alpha)}(x) = \sum_{k=0}^{n} \binom{n}{k} E_k^{(\alpha)}(0) \, x^{n-k}$.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Section 1 (generalized Euler
polynomials). -/
noncomputable def eulerPolyGen (α : ℂ) (n : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C ((Nat.choose n k : ℂ) * eulerNumGen α k) * X ^ (n - k)

/-- **Euler polynomials at (x + 1)/2 via generalized Stirling polynomials.** Let $E_n(x)$ denote
the Euler polynomial, $\alpha_k$ the Taylor coefficients of $(2 + 2z)/(2 + 2z + z^2)$, and
$S(n, k, x) = \frac{1}{k!} \sum_{j=0}^{k} \binom{k}{j} (-1)^{k-j} (x + j)^n$ the generalized
Stirling polynomial. For every $n \ge 0$, as polynomials in $x$ with rational coefficients,
$2^n E_n\left(\frac{x + 1}{2}\right) = \sum_{k=0}^{n} k! \, \alpha_k \, S(n, k, x)$.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Proposition 3.1. -/
theorem_wanted eulerPoly_half_eq_sum (n : ℕ) :
    (2 : ℚ) ^ n • (eulerPoly n).comp (C (1 / 2) * (X + 1)) =
      ∑ k ∈ Finset.range (n + 1),
        ((Nat.factorial k : ℚ) * eulerAlpha k) •
          genStirlingPoly n k

/-- **Recurrence for Euler polynomials of order α.** Let $E_m(x)$ denote the Euler polynomial
and $E_m^{(\alpha)}(x)$ the Euler polynomial of order $\alpha$. For every complex number
$\alpha$ and every integer $n \ge 1$, as polynomials in $x$,
$E_n^{(\alpha)}(x) = (x - \alpha/2) \, E_{n-1}^{(\alpha)}(x) +
\frac{\alpha}{2} \sum_{k=0}^{n-2} \binom{n-1}{k} (-1)^{n-k} E_{n-1-k}(0) \, E_k^{(\alpha)}(x)$,
where the sum is empty when $n = 1$.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Proposition 3.2. -/
theorem_wanted eulerPolyGen_recurrence (α : ℂ) (n : ℕ)
    (hn : 1 ≤ n) :
    eulerPolyGen α n =
      (X - C (α / 2)) * eulerPolyGen α (n - 1) +
        C (α / 2) * ∑ k ∈ Finset.range (n - 1),
          C ((Nat.choose (n - 1) k : ℂ) * (-1) ^ (n - k) *
            (((eulerPoly (n - 1 - k)).eval (0 : ℚ) : ℚ) : ℂ)) *
            eulerPolyGen α k

/-- **Euler polynomials as alternating sums of shifted powers.** Let $E_n(x)$ denote the Euler
polynomial. For all natural numbers $m \ge 2$ and $n \le 2m + 1$,
$E_n(x) = \sum_{k=0}^{m} \frac{(-1)^k}{2^k} \binom{m+1}{k+1}
\sum_{j=0}^{k} \binom{k}{j} \left(x + j - \frac{k+1}{2}\right)^n$
as polynomials in $x$ with rational coefficients.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Theorem 4.1. -/
theorem_wanted eulerPoly_eq_binomial_average (m n : ℕ)
    (hm : 2 ≤ m) (hn : n ≤ 2 * m + 1) :
    eulerPoly n =
      ∑ k ∈ Finset.range (m + 1),
        ((-1) ^ k * (Nat.choose (m + 1) (k + 1) : ℚ) /
            (2 : ℚ) ^ k) •
          ∑ j ∈ Finset.range (k + 1),
            (Nat.choose k j : ℚ) •
              (X + C ((j : ℚ) - (k + 1 : ℚ) / 2)) ^ n

/-- **Euler polynomials via generalized Stirling polynomials.** Let $E_n(x)$ denote the Euler
polynomial, $\alpha_k$ the Taylor coefficients of $(2 + 2z)/(2 + 2z + z^2)$, and
$S(n, k, x) = \frac{1}{k!} \sum_{j=0}^{k} \binom{k}{j} (-1)^{k-j} (x + j)^n$ the generalized
Stirling polynomial. For every integer $n \ge 1$, as polynomials in $x$ with rational
coefficients, $2^n E_n(x) = \sum_{k=0}^{n} k! \, \alpha_k \, S(n, k, 2x - 1)$.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Theorem 4.2. -/
theorem_wanted eulerPoly_eq_sum_genStirling (n : ℕ)
    (hn : 1 ≤ n) :
    (2 : ℚ) ^ n • eulerPoly n =
      ∑ k ∈ Finset.range (n + 1),
        ((Nat.factorial k : ℚ) * eulerAlpha k) •
          (genStirlingPoly n k).comp (C 2 * X - 1)

/-- **Double-sum formula for Euler polynomials.** Let $E_n(x)$ denote the Euler polynomial and
$S(n, k, x) = \frac{1}{k!} \sum_{j=0}^{k} \binom{k}{j} (-1)^{k-j} (x + j)^n$ the generalized
Stirling polynomial. For every $n \ge 0$, as polynomials in $x$ with rational coefficients,
$2^n E_n(x) = \sum_{\ell=0}^{n} \frac{(-1)^\ell}{\ell + 1}
\sum_{k=0}^{n-\ell} \frac{(k + \ell + 1)!}{2^k} \binom{\ell + 1}{k} S(n, k + \ell, 2x - 1)$.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Theorem 4.3. -/
theorem_wanted eulerPoly_eq_double_sum (n : ℕ) :
    (2 : ℚ) ^ n • eulerPoly n =
      ∑ l ∈ Finset.range (n + 1),
        ((-1) ^ l / (l + 1 : ℚ)) •
          ∑ k ∈ Finset.range (n - l + 1),
            ((Nat.factorial (k + l + 1) : ℚ) / (2 : ℚ) ^ k *
                (Nat.choose (l + 1) k : ℚ)) •
              (genStirlingPoly n (k + l)).comp (C 2 * X - 1)

end MathlibExt.NumberTheory.EulerPolynomialFormulasWanted
