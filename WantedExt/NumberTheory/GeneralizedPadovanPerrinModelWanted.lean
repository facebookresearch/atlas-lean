/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Algebra.Polynomial.Roots
public import MathlibExt.NumberTheory.GeneralizedPadovanPerrinCompanion
public import MathlibExt.NumberTheory.GeneralizedPadovanPerrinExpansion
public import MathlibExt.NumberTheory.GeneralizedPadovanPerrinFundamentalSpan
public import MathlibExt.NumberTheory.GeneralizedPadovanPerrinModel
public import MathlibExt.NumberTheory.PadovanPerrinFundamentalProduct
public import MathlibExt.NumberTheory.PadovanPerrinShiftWindow
public import MathlibExt.NumberTheory.GeneralizedPadovanPerrinModelKPadovanPerrinEqSumRoots
public import MathlibExt.NumberTheory.GeneralizedPadovanPerrinModelPadovanPerrinFundamentalEqShift
public import MathlibExt.NumberTheory.GeneralizedPadovanPerrinModelKPadovanPerrinEqSumRho

namespace MetaMathlibExt

@[expose] public section

open Polynomial

section Model

variable {R : Type*}

/-- **The Padovan–Perrin coefficient $\rho(12, 3)$ equals $5$.** Over the integers, with
$k_1 = k_2 = 1$, $p = 1$ and $s = 2$ (the Padovan–Perrin recurrence $v_n = v_{n-2} + v_{n-3}$),
the coefficient $\rho(12, 3)$ equals $5$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, equation (14) and Table 1. -/
theorem padovanPerrinRho_one_one_one_two_twelve : padovanPerrinRho (1 : ℤ) 1 1 2 12 = 5 := by
  decide

/-- **Combinatorial expression of the Padovan–Perrin sequences.** Let $R$ be a commutative ring,
let $k_1, k_2 \in R$, let $p, s$ be positive integers, and let $v \colon \mathbb{N} \to R$ satisfy
$v(n + s + p) = k_1 v(n + p) + k_2 v(n)$ for every $n$. For $0 \le m \le s + p - 1$ put
$A_m = k_2 v(m) + k_1 v(m + p)$ if $m < s$ and $A_m = k_2 v(m)$ if $m \ge s$. Let $\rho(N, s + p)$
be the Padovan–Perrin coefficient: $0$ for $N < s + p$, and for $N \ge s + p$ the sum of
$\binom{a+b}{a} k_1^a k_2^b$ over all $a, b \ge 0$ with $s a + (s + p) b = N - (s + p)$. Then for
every $n \ge s + p$,
$$v(n) = \sum_{m=0}^{s+p-1} \rho(n - m, s + p)\, A_m.$$

The paper prints the constraint in $\rho$ as $s a + (s + p) b = N - (s + p - 1)$, and with it the
identity fails (for $k_1 = k_2 = 1$, $p = 1$, $s = 2$ the printed $\rho(4, 3)$ is $1$ instead of
$0$); the constraint used here is the one of the paper's general formula (12).

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Theorem 3 (`integers-2024-A49-thm-3`). -/
public theorem_wanted padovanPerrin_eq_sum_rho [CommRing R] (k₁ k₂ : R) (p s : ℕ) (hp : 0 < p)
    (hs : 0 < s) (v : ℕ → R) (hv : (padovanPerrinRecurrence k₁ k₂ p s).IsSolution v) (n : ℕ)
    (hn : s + p ≤ n) :
    v n = ∑ m ∈ Finset.range (s + p), padovanPerrinRho k₁ k₂ p s (n - m) *
      (k₂ * v m + if m < s then k₁ * v (m + p) else 0)

/-- **The last generalized Padovan–Perrin fundamental sequence is a shifted ρ.** Let $R$ be a
commutative ring, $k_1, k_2 \in R$, and $p, s \ge 1$. Write $v^{(s+p)}$ for the $(s+p)$-th
sequence of the Fibonacci fundamental system of the $([k]; p; s)$-Padovan–Perrin recurrence and
$\rho(m, s+p)$ for the Padovan–Perrin coefficient. Then $v^{(s+p)}_n = \rho(n + 1, s + p)$ for
every $n \ge s + p$.

Here $\rho(m, s+p)$ sums over $a, b \ge 0$ with $sa + (s+p)b = m - (s+p)$, the constraint of
formula (12). With the printed constraint $m - (s + p - 1)$ the identity fails, e.g. for
$k_1 = k_2 = 1$, $p = 1$, $s = 2$, $n = 3$, where $v^{(3)}_3 = 0$ but the printed
$\rho(4, 3)$ is $1$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 4 (`integers-2024-A49-prop-4`). -/
public theorem_wanted padovanPerrinFundamental_last_eq_rho [CommRing R] (k₁ k₂ : R) (p s : ℕ)
    (hp : 0 < p) (hs : 0 < s) (n : ℕ) (hn : s + p ≤ n) :
    padovanPerrinFundamental k₁ k₂ p s (s + p) n = padovanPerrinRho k₁ k₂ p s (n + 1)

/-- **Fundamental Padovan–Perrin solutions as shifted coefficients $\rho$.** Let $R$ be a
commutative ring, let $k_1, k_2 \in R$, let $p \ge 1$ and $s$ be natural numbers, and let $j$
satisfy $p + 1 \le j \le s + p - 1$. For $1 \le \ell \le s + p$ let $v^{(\ell)}$ be the solution of
the $([k]; p; s)$-Padovan–Perrin recurrence with $v^{(\ell)}(m) = 1$ if $m + 1 = \ell$ and
$v^{(\ell)}(m) = 0$ otherwise, for $0 \le m < s + p$. Let $\rho(N, s + p)$ be the Padovan–Perrin
coefficient: $0$ for $N < s + p$, and for $N \ge s + p$ the sum of $\binom{a+b}{a} k_1^a k_2^b$
over all $a, b \ge 0$ with $s a + (s + p) b = N - (s + p)$. Then for every $n \ge 0$,
$$v^{(j)}(n) = v^{(s+p)}(n + s + p - j) = \rho(n + s + p - j + 1, s + p).$$

The paper's second clause $v^{(j)}(n) = k_2\,\rho(n + j + 1, s + p)$ for $1 \le j \le p$ is
omitted: it fails for $k_1 = 1$, $k_2 = 2$, $p = 1$, $s = 2$, $j = 1$, $n = 0$, where
$v^{(1)}(0) = 1$ but $2\rho(2, 3) = 0$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 5 (`integers-2024-A49-prop-5`). -/
public theorem_wanted padovanPerrinFundamental_eq_rho [CommRing R] (k₁ k₂ : R) (p s j : ℕ)
    (hp : 0 < p) (hpj : p + 1 ≤ j) (hjs : j ≤ s + p - 1) (n : ℕ) :
    padovanPerrinFundamental k₁ k₂ p s j n =
        padovanPerrinFundamental k₁ k₂ p s (s + p) (n + (s + p) - j) ∧
      padovanPerrinFundamental k₁ k₂ p s (s + p) (n + (s + p) - j) =
        padovanPerrinRho k₁ k₂ p s (n + (s + p) - j + 1)

/-- **Root formula for the generalized Padovan–Perrin coefficients ρ.** Let $k_1, k_2$ be complex
numbers with $k_2 \neq 0$, let $p, s \ge 1$, and let $P(z) = z^{s+p} - k_1 z^p - k_2$. If $P$ is
separable, that is, has $s + p$ distinct roots $\lambda_1, \dots, \lambda_{s+p}$ in $\mathbb{C}$,
then for every $n \ge s + p$ the Padovan–Perrin coefficient satisfies

$$\rho(n, s + p) = \sum_{i=1}^{s+p} \frac{\lambda_i^{n-1}}{P'(\lambda_i)}.$$

The paper states this for the general $\rho$ of formula (12) attached to an arbitrary
characteristic polynomial $z^r - a_0 z^{r-1} - \cdots - a_{r-1}$; this is its specialization to
the $([k]; p; s)$-Padovan–Perrin coefficients, the case the paper applies.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Lemma 5 (`integers-2024-A49-lem-5`). -/
public theorem_wanted padovanPerrinRho_eq_sum_roots (k₁ k₂ : ℂ) (p s : ℕ) (hp : 0 < p)
    (hs : 0 < s) (hk₂ : k₂ ≠ 0) (hsep : (X ^ (s + p) - C k₁ * X ^ p - C k₂).Separable) (n : ℕ)
    (hn : s + p ≤ n) :
    padovanPerrinRho k₁ k₂ p s n =
      ((X ^ (s + p) - C k₁ * X ^ p - C k₂).roots.map fun x =>
        x ^ (n - 1) / (derivative (X ^ (s + p) - C k₁ * X ^ p - C k₂)).eval x).sum

/-- **Analytic expression of the Padovan–Perrin sequences.** Let $k_1, k_2, p, s$ be natural
numbers with $k_1 > 0$, $p \ge 2$, $p < s$ and $k_1^2 < k_2$, let
$P(z) = z^{s+p} - k_1 z^p - k_2$, and let $v \colon \mathbb{N} \to \mathbb{C}$ satisfy
$v(n + s + p) = k_1 v(n + p) + k_2 v(n)$ for every $n$. For $0 \le m \le s + p - 1$ put
$A_m = k_2 v(m) + k_1 v(m + p)$ if $m < s$ and $A_m = k_2 v(m)$ if $m \ge s$. Then for every
$n \ge s + p$,
$$v(n) = \sum_{m=0}^{s+p-1} A_m \sum_{\lambda} \frac{\lambda^{n-1-m}}{P'(\lambda)},$$
where $\lambda$ runs over the complex roots of $P$ counted with multiplicity.

The paper assumes that the roots of $P$ are distinct; this follows from the other hypotheses
(Lemma 4 of the paper).

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 6 (`integers-2024-A49-prop-6`). -/
public theorem_wanted padovanPerrin_eq_sum_roots (k₁ k₂ p s : ℕ) (hk₁ : 0 < k₁) (hp : 2 ≤ p)
    (hps : p < s) (hk : k₁ ^ 2 < k₂) (v : ℕ → ℂ)
    (hv : (padovanPerrinRecurrence (k₁ : ℂ) (k₂ : ℂ) p s).IsSolution v) (n : ℕ)
    (hn : s + p ≤ n) :
    v n = ∑ m ∈ Finset.range (s + p),
      ((k₂ : ℂ) * v m + if m < s then (k₁ : ℂ) * v (m + p) else 0) *
        ((X ^ (s + p) - C (k₁ : ℂ) * X ^ p - C (k₂ : ℂ)).roots.map fun x =>
          x ^ (n - 1 - m) /
            (derivative (X ^ (s + p) - C (k₁ : ℂ) * X ^ p - C (k₂ : ℂ))).eval x).sum

/-- **Fundamental $k$-Padovan–Perrin solutions as coefficients $\rho$.** Let $R$ be a commutative
ring and $k \in R$, and take the Padovan–Perrin recurrence with $k_1 = 1$, $k_2 = k$, $p = 1$,
$s = 2$, that is, $v(n + 3) = v(n + 1) + k\,v(n)$. Let $v^{(2)}$ and $v^{(3)}$ be its solutions
with initial values $(v^{(2)}(0), v^{(2)}(1), v^{(2)}(2)) = (0, 1, 0)$ and
$(v^{(3)}(0), v^{(3)}(1), v^{(3)}(2)) = (0, 0, 1)$. Let $\rho(m) = \rho(m, 3)$ be the
Padovan–Perrin coefficient for these parameters: $\rho(m) = 0$ for $m < 3$, and for $m \ge 3$ it
is the sum of $\binom{a+b}{a} k^b$ over all $a, b \ge 0$ with $2a + 3b = m - 3$. Then for every
$n \ge 0$, $v^{(3)}(n) = \rho(n + 1)$ and $v^{(2)}(n) = \rho(n + 2)$.

The paper's third formula $v^{(1)}(n) = k\,\rho(n + 2)$, for the solution $v^{(1)}$ with initial
values $(1, 0, 0)$, is omitted: it fails for $k = 2$, $n = 0$ ($v^{(1)}(0) = 1$, $2\rho(2) = 0$).
The paper takes $k \ge 2$ an integer.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 9 (`integers-2024-A49-prop-9`). -/
public theorem_wanted kPadovanPerrinFundamental_eq_rho [CommRing R] (k : R) (n : ℕ) :
    padovanPerrinFundamental 1 k 1 2 3 n = padovanPerrinRho 1 k 1 2 (n + 1) ∧
      padovanPerrinFundamental 1 k 1 2 2 n = padovanPerrinRho 1 k 1 2 (n + 2)

end Model

end

end MetaMathlibExt
