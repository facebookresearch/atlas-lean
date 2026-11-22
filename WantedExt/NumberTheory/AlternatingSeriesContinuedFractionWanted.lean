/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Data.EReal.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

namespace MetaMathlibExt

@[expose] public section

/-- **Alternating series with a two-step continued fraction pattern.** Let $(u_i)_{i \ge 0}$ be
positive integers with $u_0 = 1$, and let $x$ be an irrational real number with
$\sum_{i \ge 0} (-1)^i / u_i = x$. Write $x = [a_0; a_1, a_2, \dots]$ for its continued fraction
expansion and $p_n / q_n = [a_0; a_1, \dots, a_n]$ for its convergents, with $q_0 = 1$ and
$q_1 = a_1$. Suppose that for every $n \ge 0$ we have
$\sum_{i=0}^{n} (-1)^i / u_i = p_{n+1} / q_{n+1}$, $u_{2n+1} \mid u_{2n+2}$ and
$u_{2n+3} = \bigl(\prod_{j=0}^{n} u_{2j+2} / u_{2j+1}\bigr)^2 + u_{2n+2}$. Then
(i) $u_n = q_n q_{n+1}$ for every $n \ge 0$, (ii) for every $n \ge 0$ there is a natural number
$m$ with $a_{2n+3} = m \, q_{2n+1}$, and (iii) $a_{2n+2} = 1$ for every $n \ge 1$.

Part (iii) is stated only for $n \ge 1$, because it can fail at $n = 0$: the continued fraction
$[0; 1, 2, 1, 1, 4, 1, 32, 1, 1280, \dots]$, continued by $a_{2n+4} = 1$ and
$a_{2n+3} = q_{2n+1}$, with $u_n = q_n q_{n+1}$ (here $q = 1, 1, 3, 4, 7, 32, 39, 1280, \dots$)
satisfies every hypothesis and has $a_2 = 2$.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Theorem 4 (`jis-2025-25.1.4-thm-4`). -/
public theorem_wanted alternatingSeries_contFract_twoStepPattern (x : ℝ) (hirr : Irrational x)
    (u : ℕ → ℕ) (hu : ∀ i, 0 < u i) (hu₀ : u 0 = 1)
    (hsum : HasSum (fun i : ℕ => (-1 : ℝ) ^ i / u i) x)
    (hconv : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i / u i =
      (GenContFract.of x).nums (n + 1) / (GenContFract.of x).dens (n + 1))
    (hdvd : ∀ n : ℕ, u (2 * n + 1) ∣ u (2 * n + 2))
    (hrec : ∀ n : ℕ, (u (2 * n + 3) : ℚ) =
      (∏ j ∈ Finset.range (n + 1), (u (2 * j + 2) : ℚ) / u (2 * j + 1)) ^ 2 + u (2 * n + 2)) :
    (∀ n : ℕ, (u n : ℝ) = (GenContFract.of x).dens n * (GenContFract.of x).dens (n + 1)) ∧
      (∀ n : ℕ, ∃ m : ℕ, (GenContFract.of x).partDens.get? (2 * n + 2) =
        some ((GenContFract.of x).dens (2 * n + 1) * m)) ∧
      ∀ n : ℕ, 1 ≤ n → (GenContFract.of x).partDens.get? (2 * n + 1) = some 1

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

/-- **Convergent denominators of the two-step pattern.** For a natural number $\beta$ and a
sequence $(\omega_n)_{n \ge 0}$ of natural numbers, define natural numbers $q_n$ by $q_0 = 1$,
$q_1 = \omega_0$, and for every $n \ge 0$, $q_{2n+2} = q_{2n+1} + q_{2n}$ and
$q_{2n+3} = \omega_{n+1} q_{2n+1}^\beta q_{2n+2} + q_{2n+1}$.

When the $\omega_n$ are positive, these are the convergent denominators of the continued fraction
$[0; \omega_0, 1, \omega_1 q_1^\beta, 1, \omega_2 q_3^\beta, 1, \dots]$.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Section 2.1, displays (e2) and (e22). -/
public def twoStepPatternDen (β : ℕ) (ω : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => ω 0
  | n + 2 => if n % 2 = 0 then twoStepPatternDen β ω (n + 1) + twoStepPatternDen β ω n
      else ω (n / 2 + 1) * twoStepPatternDen β ω n ^ β * twoStepPatternDen β ω (n + 1) +
        twoStepPatternDen β ω n

/-- **Small values of the two-step pattern denominators.** For $\beta = 1$ and $\omega_n = 1$ for
all $n$, the convergent denominators $q_0, \dots, q_7$ of the two-step pattern are
$1, 1, 2, 3, 5, 18, 23, 432$ (the paper's first example).

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Section 2.1, first example. -/
public theorem twoStepPatternDen_one_one :
    (List.range 8).map (twoStepPatternDen 1 fun _ => 1) = [1, 1, 2, 3, 5, 18, 23, 432] := by
  decide

/-- **Convergent denominators of the three-step pattern.** For a natural number $\beta$ and a
sequence $(\omega_n)_{n \ge 0}$ of natural numbers, define natural numbers $q_n$ by $q_0 = 1$,
$q_1 = \omega_0$, and for every $n \ge 0$, $q_{3n+2} = q_{3n+1} + q_{3n}$,
$q_{3n+3} = q_{3n+2} + q_{3n+1}$ and $q_{3n+4} = \omega_{n+1} q_{3n+3} q_{3n+2}^\beta + q_{3n+2}$.

When the $\omega_n$ are positive, these are the convergent denominators of the continued fraction
$[0; \omega_0, 1, 1, \omega_1 q_2^\beta, 1, 1, \omega_2 q_5^\beta, \dots]$.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Section 2.2, displays (e3) and (e33). -/
public def threeStepPatternDen (β : ℕ) (ω : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => ω 0
  | n + 2 => if n % 3 = 2 then
        ω (n / 3 + 1) * threeStepPatternDen β ω (n + 1) * threeStepPatternDen β ω n ^ β +
          threeStepPatternDen β ω n
      else threeStepPatternDen β ω (n + 1) + threeStepPatternDen β ω n

/-- **Small values of the three-step pattern denominators.** For $\beta = 1$ and $\omega_n = 1$
for all $n$, the convergent denominators $q_0, \dots, q_7$ of the three-step pattern are
$1, 1, 2, 3, 8, 11, 19, 220$.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Section 2.2, display (e33). -/
public theorem threeStepPatternDen_one_one :
    (List.range 8).map (threeStepPatternDen 1 fun _ => 1) = [1, 1, 2, 3, 8, 11, 19, 220] := by
  decide

/-- **Two-step pattern as an alternating series.** Let $\beta$ be a natural number, let
$(\omega_n)_{n \ge 0}$ be positive integers, and let $(q_n)_{n \ge 0}$ be the convergent
denominators of the two-step pattern for $\beta$ and $(\omega_n)$. Then the series
$\sum_{i \ge 0} (-1)^i / (q_i q_{i+1})$ converges absolutely, and its sum $x$ has continued
fraction expansion $[a_0; a_1, a_2, \dots]$ with $a_0 = 0$, $a_1 = \omega_0$, and
$a_{2n+2} = 1$ and $a_{2n+3} = \omega_{n+1} q_{2n+1}^\beta$ for every $n \ge 0$; that is,
$x = [0; \omega_0, 1, \omega_1 q_1^\beta, 1, \omega_2 q_3^\beta, 1, \dots]$.

The paper assumes $\beta \ge 1$; the statement here also allows $\beta = 0$.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Proposition 2, under the hypotheses (e2) of Section 2.1. -/
public theorem_wanted twoStepPattern_alternatingSeries_contFract (β : ℕ) (ω : ℕ → ℕ)
    (hω : ∀ n, 0 < ω n) :
    let q := twoStepPatternDen β ω
    let x := ∑' i : ℕ, (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))
    Summable (fun i : ℕ => (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))) ∧
      (GenContFract.of x).h = 0 ∧ (GenContFract.of x).partDens.get? 0 = some (ω 0 : ℝ) ∧
      ∀ n : ℕ, (GenContFract.of x).partDens.get? (2 * n + 1) = some 1 ∧
        (GenContFract.of x).partDens.get? (2 * n + 2) = some ((ω (n + 1) : ℝ) * q (2 * n + 1) ^ β)

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

/-- **Three-step pattern as an alternating series.** Let $\beta$ be a natural number, let
$(\omega_n)_{n \ge 0}$ be positive integers, and let $(q_n)_{n \ge 0}$ be the convergent
denominators of the three-step pattern for $\beta$ and $(\omega_n)$. Then the series
$\sum_{i \ge 0} (-1)^i / (q_i q_{i+1})$ converges absolutely, and its sum $x$ has continued
fraction expansion $[a_0; a_1, a_2, \dots]$ with $a_0 = 0$, $a_1 = \omega_0$, and
$a_{3n+2} = a_{3n+3} = 1$ and $a_{3n+4} = \omega_{n+1} q_{3n+2}^\beta$ for every $n \ge 0$; that is,
$x = [0; \omega_0, 1, 1, \omega_1 q_2^\beta, 1, 1, \omega_2 q_5^\beta, \dots]$.

The paper assumes $\beta \ge 1$; the statement here also allows $\beta = 0$.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Proposition 8, under the hypotheses (e3) of Section 2.2. -/
public theorem_wanted threeStepPattern_alternatingSeries_contFract (β : ℕ) (ω : ℕ → ℕ)
    (hω : ∀ n, 0 < ω n) :
    let q := threeStepPatternDen β ω
    let x := ∑' i : ℕ, (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))
    Summable (fun i : ℕ => (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))) ∧
      (GenContFract.of x).h = 0 ∧ (GenContFract.of x).partDens.get? 0 = some (ω 0 : ℝ) ∧
      ∀ n : ℕ, (GenContFract.of x).partDens.get? (3 * n + 1) = some 1 ∧
        (GenContFract.of x).partDens.get? (3 * n + 2) = some 1 ∧
        (GenContFract.of x).partDens.get? (3 * n + 3) = some ((ω (n + 1) : ℝ) * q (3 * n + 2) ^ β)

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
