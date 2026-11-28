/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.AlternatingSeriesContinuedFraction
public import MathlibExt.NumberTheory.AlternatingSeriesContinuedFractionTwoStepPattern
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Data.EReal.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

namespace MetaMathlibExt

@[expose] public section

/-- **Alternating series with a three-step continued fraction pattern.** Let $(u_i)_{i \ge 0}$
be positive integers with $u_0 = 1$, and let $x$ be an irrational real number with
$\sum_{i \ge 0} (-1)^i / u_i = x$. Write $x = [a_0; a_1, a_2, \dots]$ for its continued fraction
expansion and $p_n / q_n = [a_0; a_1, \dots, a_n]$ for its convergents, with $q_0 = 1$ and
$q_1 = a_1$. Suppose that for every $n \ge 0$ we have
$\sum_{i=0}^{n} (-1)^i / u_i = p_{n+1} / q_{n+1}$, $u_{3n+2} \mid u_{3n+3}$,
$u_{3n+2} - u_{3n+1} = \bigl(\prod_{j=0}^{\lfloor 3n/2 \rfloor} u_{3n-2j+1} / u_{3n-2j}\bigr)^2$
and $u_{3n+4} - u_{3n+3} = (u_{3n+3} / u_{3n+2})^2 (u_{3n+2} - u_{3n+1})$. Then
(i) $u_n = q_n q_{n+1}$ for every $n \ge 0$, (ii) for every $n \ge 0$ there is a natural number
$m$ with $a_{3n+4} = m \, q_{3n+2}$, and (iii) $a_{3n+3} = 1$ for every $n \ge 0$ and
$a_{3n+2} = 1$ for every $n \ge 1$.

The product runs over the quotients $u_{k+1} / u_k$ for $k = 3n, 3n - 2, 3n - 4, \dots$, ending
at $k = 1$ when $n$ is odd and at $k = 0$ when $n$ is even. The condition $a_{3n+2} = 1$ is
stated only for $n \ge 1$, because it can fail at $n = 0$: the continued fraction
$[0; 1, 2, 1, 3, 1, 1, 19, 1, 1, 699, \dots]$ with $u_n = q_n q_{n+1}$ satisfies every hypothesis
and has $a_2 = 2$.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Theorem 10 (`jis-2025-25.1.4-thm-10`). -/
public theorem_wanted alternatingSeries_contFract_threeStepPattern (x : ℝ) (hirr : Irrational x)
    (u : ℕ → ℕ) (hu : ∀ i, 0 < u i) (hu₀ : u 0 = 1)
    (hsum : HasSum (fun i : ℕ => (-1 : ℝ) ^ i / u i) x)
    (hconv : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i / u i =
      (GenContFract.of x).nums (n + 1) / (GenContFract.of x).dens (n + 1))
    (hdvd : ∀ n : ℕ, u (3 * n + 2) ∣ u (3 * n + 3))
    (hrec₁ : ∀ n : ℕ, (u (3 * n + 2) : ℚ) - u (3 * n + 1) =
      (∏ j ∈ Finset.range (3 * n / 2 + 1), (u (3 * n - 2 * j + 1) : ℚ) / u (3 * n - 2 * j)) ^ 2)
    (hrec₂ : ∀ n : ℕ, (u (3 * n + 4) : ℚ) - u (3 * n + 3) =
      ((u (3 * n + 3) : ℚ) / u (3 * n + 2)) ^ 2 * (u (3 * n + 2) - u (3 * n + 1))) :
    (∀ n : ℕ, (u n : ℝ) = (GenContFract.of x).dens n * (GenContFract.of x).dens (n + 1)) ∧
      (∀ n : ℕ, ∃ m : ℕ, (GenContFract.of x).partDens.get? (3 * n + 3) =
        some ((GenContFract.of x).dens (3 * n + 2) * m)) ∧
      (∀ n : ℕ, (GenContFract.of x).partDens.get? (3 * n + 2) = some 1) ∧
      ∀ n : ℕ, 1 ≤ n → (GenContFract.of x).partDens.get? (3 * n + 1) = some 1

/-- **Irrationality exponent of the two-step pattern.** Let $\beta \ge 1$ be a natural number,
let $(\omega_n)_{n \ge 0}$ be positive integers, let $(q_n)_{n \ge 0}$ be the convergent
denominators of the two-step pattern for $\beta$ and $(\omega_n)$, and let
$x = \sum_{i \ge 0} (-1)^i / (q_i q_{i+1})$. Let $L$ be the limit superior, in the extended real
numbers, of $\ln \omega_n / \ln q_{2n}$ as $n \to \infty$. Then $x$ is Liouville with exponent $p$
for every real $p < 2 + \beta + L$, that is, for each such $p$ there is a constant $C$ such that
$0 < |x - m/k| < C / k^p$ for infinitely many positive integers $k$, each with some integer $m$.
Moreover $2 + \beta \le 2 + \beta + L$, and $x$ is transcendental.

In other words, the irrationality exponent of $x$ satisfies $\mu(x) \ge 2 + \beta + L$, where $L$
may be $+\infty$.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Theorem 3. -/
public theorem_wanted twoStepPattern_irrationalityExponent (β : ℕ) (hβ : 1 ≤ β) (ω : ℕ → ℕ)
    (hω : ∀ n, 0 < ω n) :
    let q := twoStepPatternDen β ω
    let x := ∑' i : ℕ, (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))
    let L : EReal := Filter.limsup (fun n : ℕ =>
      ((Real.log (ω n) / Real.log (q (2 * n)) : ℝ) : EReal)) Filter.atTop
    (∀ p : ℝ, (p : EReal) < 2 + β + L → LiouvilleWith p x) ∧
      (2 + β : EReal) ≤ 2 + β + L ∧ Transcendental ℤ x

/-- **Irrationality exponent of the three-step pattern.** Let $\beta \ge 1$ be a natural number,
let $(\omega_n)_{n \ge 0}$ be positive integers, let $(q_n)_{n \ge 0}$ be the convergent
denominators of the three-step pattern for $\beta$ and $(\omega_n)$, and let
$x = \sum_{i \ge 0} (-1)^i / (q_i q_{i+1})$. Let $L$ be the limit superior, in the extended real
numbers, of $\ln \omega_n / \ln q_{3n}$ as $n \to \infty$. Then $x$ is Liouville with exponent $p$
for every real $p < 2 + \beta + L$, that is, for each such $p$ there is a constant $C$ such that
$0 < |x - m/k| < C / k^p$ for infinitely many positive integers $k$, each with some integer $m$.
Moreover $2 + \beta \le 2 + \beta + L$, and $x$ is transcendental.

In other words, the irrationality exponent of $x$ satisfies $\mu(x) \ge 2 + \beta + L$, where $L$
may be $+\infty$.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Theorem 9. -/
public theorem_wanted threeStepPattern_irrationalityExponent (β : ℕ) (hβ : 1 ≤ β) (ω : ℕ → ℕ)
    (hω : ∀ n, 0 < ω n) :
    let q := threeStepPatternDen β ω
    let x := ∑' i : ℕ, (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))
    let L : EReal := Filter.limsup (fun n : ℕ =>
      ((Real.log (ω n) / Real.log (q (3 * n)) : ℝ) : EReal)) Filter.atTop
    (∀ p : ℝ, (p : EReal) < 2 + β + L → LiouvilleWith p x) ∧
      (2 + β : EReal) ≤ 2 + β + L ∧ Transcendental ℤ x

end

end MetaMathlibExt
