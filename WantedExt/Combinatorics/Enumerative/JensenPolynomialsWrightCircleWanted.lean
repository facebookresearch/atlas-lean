/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import MathlibExt.Analysis.SpecialFunctions.Gamma.TwistedDigamma
public import MathlibExt.Combinatorics.Enumerative.JensenHyperbolicity

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
