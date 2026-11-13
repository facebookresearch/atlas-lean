/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Jensen polynomials of coefficients from Wright's circle method

Statement-only requests from Bal, Haraldson, Males and Thompson's paper on hyperbolicity of
Jensen polynomials. The Jensen polynomial of degree `d` and shift `n` of a sequence `α` is
`J_α^{d,n}(X) = ∑_{j=0}^{d} (d choose j) α(n + j) Xʲ` (Griffin, Ono, Rolen and Zagier); it is
written out in each statement. A real polynomial is hyperbolic when all of its roots are real,
written `p.roots.card = p.natDegree`.
-/

open Filter Asymptotics Polynomial

namespace MetaMathlibExt

@[expose] public section

/-- **An integral formula for $\log \Gamma(1/N)$.** For every real number $N > 0$,
$$
\int_0^\infty \left( \frac{e^{-x}}{x \left(1 - e^{-N x}\right)} - \frac{1}{N x^2} -
\left( \frac{1}{2} - \frac{1}{N} \right) \frac{e^{-x}}{x} \right) dx =
\log \Gamma\left( \frac{1}{N} \right) + \left( \frac{1}{2} - \frac{1}{N} \right) \log \frac{1}{N} -
\frac{1}{2} \log (2\pi).
$$

Source: Jashan Bal, Fern Haraldson, Joshua Males and Ian Thompson, *Jensen Polynomials Associated
with Wright's Circle Method: Hyperbolicity and Turán Inequalities*, INTEGERS 25 (2025),
Article A36, Lemma 2 (`integers-2025-A36-lem-2`). -/
public theorem_wanted integral_exp_div_one_sub_exp_sub_eq_log_Gamma {N : ℝ} (hN : 0 < N) :
    ∫ x in Set.Ioi (0 : ℝ),
        (Real.exp (-x) / (x * (1 - Real.exp (-(N * x)))) - 1 / (N * x ^ 2) -
          (1 / 2 - 1 / N) * Real.exp (-x) / x) =
      Real.log (Real.Gamma (1 / N)) + (1 / 2 - 1 / N) * Real.log (1 / N) -
        1 / 2 * Real.log (2 * Real.pi)

/-- **A twisted sum of digamma values.** Let $p$ and $k$ be natural numbers with $1 \le k < p$,
and let $\psi = \Gamma'/\Gamma$ be the digamma function. Then
$$
\sum_{\alpha=1}^{p} e^{2\pi i k \alpha / p} \, \psi\left( \frac{\alpha}{p} \right) =
p \operatorname{Log}\left( 1 - e^{2\pi i k / p} \right),
$$
where $\operatorname{Log}$ is the principal branch of the complex logarithm.

Source: Jashan Bal, Fern Haraldson, Joshua Males and Ian Thompson, *Jensen Polynomials Associated
with Wright's Circle Method: Hyperbolicity and Turán Inequalities*, INTEGERS 25 (2025),
Article A36, Lemma 3 (`integers-2025-A36-lem-3`). -/
public theorem_wanted sum_exp_mul_digamma_div_eq_mul_log_one_sub {p k : ℕ} (hk : 1 ≤ k)
    (hkp : k < p) :
    ∑ α ∈ Finset.Icc 1 p,
        Complex.exp (2 * Real.pi * Complex.I * k * α / p) * Complex.digamma (α / p) =
      p * Complex.log (1 - Complex.exp (2 * Real.pi * Complex.I * k / p))

/-- **Hyperbolicity of Jensen polynomials from a log-ratio expansion.** Let $\alpha$, $A$ and
$\delta$ be sequences of positive real numbers indexed by $n \in \mathbb{N}$ with
$\delta(n) \to 0$, let $d \ge 1$ be an integer, and for $3 \le j \le d$ let $g_j$ be a real
sequence with $g_j(n) = o(\delta(n)^j)$ as $n \to \infty$. Suppose that for every natural number
$k \le d$,
$$
\log \frac{\alpha(n + k)}{\alpha(n)} = A(n) k - \delta(n)^2 k^2 + \sum_{j=3}^{d} g_j(n) k^j +
o(\delta(n)^d)
$$
as $n \to \infty$. Then for all sufficiently large $n$ the Jensen polynomial
$J_\alpha^{d,n}(X) = \sum_{j=0}^{d} \binom{d}{j} \alpha(n + j) X^j$ is hyperbolic: the number of
its real roots, counted with multiplicity, equals its degree.

The source also proves that suitably renormalized Jensen polynomials converge to the Hermite
polynomials; that conclusion is not part of this statement.

Source: Jashan Bal, Fern Haraldson, Joshua Males and Ian Thompson, *Jensen Polynomials Associated
with Wright's Circle Method: Hyperbolicity and Turán Inequalities*, INTEGERS 25 (2025),
Article A36, Theorem 5 (`integers-2025-A36-thm-5`), quoted there from Griffin, Ono, Rolen and
Zagier. -/
public theorem_wanted eventually_jensen_hyperbolic_of_log_ratio_expansion {α A δ : ℕ → ℝ}
    (hα : ∀ n, 0 < α n) (hA : ∀ n, 0 < A n) (hδ : ∀ n, 0 < δ n)
    (hδ0 : Tendsto δ atTop (nhds 0)) {d : ℕ} (hd : 1 ≤ d) (g : ℕ → ℕ → ℝ)
    (hg : ∀ j ∈ Finset.Icc 3 d, g j =o[atTop] fun n => δ n ^ j)
    (hexp : ∀ k ≤ d, (fun n => Real.log (α (n + k) / α n) -
        (A n * k - δ n ^ 2 * k ^ 2 + ∑ j ∈ Finset.Icc 3 d, g j n * (k : ℝ) ^ j)) =o[atTop]
      fun n => δ n ^ d) :
    ∀ᶠ n in atTop,
      (∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) * α (n + j)) * X ^ j).roots.card =
        (∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) * α (n + j)) * X ^ j).natDegree

/-- **Eventual hyperbolicity for colored partitions.** Let $r \ge 1$ and $d \ge 1$ be integers. For
$m \in \mathbb{N}$ let
$$
C_r(m) = \sum_{m_1 + \dots + m_r = m} p(m_1) \cdots p(m_r)
$$
be the number of $r$-colored partitions of $m$, where the sum runs over all $r$-tuples of natural
numbers with sum $m$ and $p$ is the partition function. Then for all sufficiently large $n$ the
Jensen polynomial $J^{d,n}(X) = \sum_{j=0}^{d} \binom{d}{j} C_r(n + j) X^j$ is hyperbolic: the
number of its real roots, counted with multiplicity, equals its degree.

In the source, $C_r(n)$ is the coefficient of $q^{tn}$ in $1/(q^t; q^t)_\infty^r$ for any
$t \ge 1$; the source also proves a Hermite-limit statement and higher order Turán inequalities,
which are not part of this statement.

Source: Jashan Bal, Fern Haraldson, Joshua Males and Ian Thompson, *Jensen Polynomials Associated
with Wright's Circle Method: Hyperbolicity and Turán Inequalities*, INTEGERS 25 (2025),
Article A36, Theorem 3, part 1 (`integers-2025-A36-thm-3`). -/
public theorem_wanted eventually_jensen_hyperbolic_coloredPartitions {r : ℕ} (hr : 1 ≤ r)
    {d : ℕ} (hd : 1 ≤ d) :
    ∀ᶠ n in atTop,
      (∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) *
          ((∑ x ∈ Finset.Nat.antidiagonalTuple r (n + j),
            ∏ i, Fintype.card (Nat.Partition (x i)) : ℕ) : ℝ)) * X ^ j).roots.card =
        (∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) *
          ((∑ x ∈ Finset.Nat.antidiagonalTuple r (n + j),
            ∏ i, Fintype.card (Nat.Partition (x i)) : ℕ) : ℝ)) * X ^ j).natDegree

open scoped Classical in
/-- **Eventual hyperbolicity for partitions into parts $\equiv a \pmod{p}$.** Let $p$ be a prime,
let $a$ be an integer with $1 \le a < p$, and let $d \ge 1$ be an integer. For $m \in \mathbb{N}$
let $b_{a,p}(m)$ be the number of partitions of $m$ all of whose parts are congruent to $a$
modulo $p$. Then for all sufficiently large $n$ the Jensen polynomial
$J^{d,n}(X) = \sum_{j=0}^{d} \binom{d}{j} b_{a,p}(n + j) X^j$ is hyperbolic: the number of its
real roots, counted with multiplicity, equals its degree.

In the source, $b_{a,p}(n)$ is the coefficient of $q^n$ in $1/(q^a; q^p)_\infty$, and the case
$a = 0$ is also admitted there, although $(1; q^p)_\infty = 0$; the source also gives an asymptotic
formula, a Hermite-limit statement and higher order Turán inequalities, which are not part of
this statement.

Source: Jashan Bal, Fern Haraldson, Joshua Males and Ian Thompson, *Jensen Polynomials Associated
with Wright's Circle Method: Hyperbolicity and Turán Inequalities*, INTEGERS 25 (2025),
Article A36, Theorem 4, part 2 (`integers-2025-A36-thm-4`). -/
public theorem_wanted eventually_jensen_hyperbolic_partitions_parts_mod {p a : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) (hap : a < p) {d : ℕ} (hd : 1 ≤ d) :
    ∀ᶠ n in atTop,
      (∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) *
          ((Finset.univ.filter fun π : Nat.Partition (n + j) =>
            ∀ i ∈ π.parts, i % p = a).card : ℝ)) * X ^ j).roots.card =
        (∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) *
          ((Finset.univ.filter fun π : Nat.Partition (n + j) =>
            ∀ i ∈ π.parts, i % p = a).card : ℝ)) * X ^ j).natDegree

end

end MetaMathlibExt
