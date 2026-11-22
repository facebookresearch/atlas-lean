/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Integral values of generating functions of Fibonacci polynomials

Statements from Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating
Functions of Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024.

For positive integers `a`, `b` the paper's polynomials `F_i(x)` (`F_0 = 0`, `F_1 = 1`) and
`L_i(x)` (`L_0 = 2`, `L_1 = ax`), both with `G_{i+2}(x) = ax G_{i+1}(x) + b G_i(x)`, are the
existing `generalizedFibonacciPolynomial` sequences over `ℤ[X]`. The generating functions are the
rational functions `f(x, t) = t / (1 - axt - bt²)` and `l(x, t) = (2 - axt) / (1 - axt - bt²)`.
The paper's case `d = 1` of its `√d` sequences is the evaluation at `x = 1`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
public import MathlibExt.NumberTheory.LucasSequence

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- The paper's Fibonacci polynomials `F_i(x)` with parameters `a`, `b`. -/
local notation "𝔽[" a ", " b "]" =>
  generalizedFibonacciPolynomial 0 1 (C ((a : ℕ) : ℤ) * X) (C ((b : ℕ) : ℤ))

/-- The paper's Lucas polynomials `L_i(x)` with parameters `a`, `b`. -/
local notation "𝕃[" a ", " b "]" =>
  generalizedFibonacciPolynomial 2 (C ((a : ℕ) : ℤ) * X) (C ((a : ℕ) : ℤ) * X) (C ((b : ℕ) : ℤ))

/-- A polynomial with integer coefficients, viewed as a rational function over `ℚ`. -/
local notation:max "ι" p:max => algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.map (Int.castRingHom ℚ) p)

/-- **Integer-polynomial values of the Fibonacci polynomial generating function.** Let $a$ and $b$
be positive integers with $b \mid a$, let $F_i(x) \in \mathbb{Z}[x]$ be the polynomials with
$F_0 = 0$, $F_1 = 1$ and $F_{i+2} = ax\,F_{i+1} + b\,F_i$ for all $i \ge 0$, and let
$f(x, t) = t / (1 - axt - bt^2)$. For a rational function $q(x) \in \mathbb{Q}(x)$, the rational
function $f(x, q(x))$ is a polynomial with integer coefficients if and only if
$q(x) = F_i(x) / F_{i+1}(x)$ for some $i \in \mathbb{N}$ or
$q(x) = -F_{i+1}(x) / (b F_i(x))$ for some $i \ge 1$.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024, Theorem 1.2
(`fq-2024-tsuno05142024-thm-1.2`). -/
public theorem_wanted fibonacciPolyGenFun_mem_intPoly_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hba : b ∣ a) (q : RatFunc ℚ) :
    (∃ P : ℤ[X], q / (1 - (a : RatFunc ℚ) * RatFunc.X * q - (b : RatFunc ℚ) * q ^ 2) = ι P) ↔
      (∃ i : ℕ, q = ι (𝔽[a, b] i) / ι (𝔽[a, b] (i + 1))) ∨
        ∃ i : ℕ, 0 < i ∧ q = -ι (𝔽[a, b] (i + 1)) / ((b : RatFunc ℚ) * ι (𝔽[a, b] i))

/-- **Integer-polynomial values of the Lucas polynomial generating function.** Let $a$ and $b$ be
positive integers with $b \mid a$, let $F_i(x), L_i(x) \in \mathbb{Z}[x]$ be the polynomials with
$F_0 = 0$, $F_1 = 1$, $L_0 = 2$, $L_1 = ax$ and $G_{i+2} = ax\,G_{i+1} + b\,G_i$ for $G = F, L$
and all $i \ge 0$, and let $l(x, t) = (2 - axt) / (1 - axt - bt^2)$. For a rational function
$q(x) \in \mathbb{Q}(x)$, the rational function $l(x, q(x))$ is a polynomial with integer
coefficients if and only if $q(x)$ is one of $F_i(x) / F_{i+1}(x)$, $L_i(x) / L_{i+1}(x)$ and
$-L_{i+1}(x) / (b L_i(x))$ for some $i \in \mathbb{N}$, or $q(x) = -F_{i+1}(x) / (b F_i(x))$ for
some $i \ge 1$.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024, Theorem 1.3
(`fq-2024-tsuno05142024-thm-1.3`). -/
public theorem_wanted lucasPolyGenFun_mem_intPoly_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hba : b ∣ a) (q : RatFunc ℚ) :
    (∃ P : ℤ[X], (2 - (a : RatFunc ℚ) * RatFunc.X * q) /
        (1 - (a : RatFunc ℚ) * RatFunc.X * q - (b : RatFunc ℚ) * q ^ 2) = ι P) ↔
      (∃ i : ℕ, q = ι (𝔽[a, b] i) / ι (𝔽[a, b] (i + 1)) ∨
          q = ι (𝕃[a, b] i) / ι (𝕃[a, b] (i + 1)) ∨
          q = -ι (𝕃[a, b] (i + 1)) / ((b : RatFunc ℚ) * ι (𝕃[a, b] i))) ∨
        ∃ i : ℕ, 0 < i ∧ q = -ι (𝔽[a, b] (i + 1)) / ((b : RatFunc ℚ) * ι (𝔽[a, b] i))

/-- **Integer values of the generalized Fibonacci generating function at rationals.** Let $a$ and
$b$ be positive integers with $b \mid a$, and let $F_i(x) \in \mathbb{Z}[x]$ be the polynomials
with $F_0 = 0$, $F_1 = 1$ and $F_{i+2} = ax\,F_{i+1} + b\,F_i$ for all $i \ge 0$. For a rational
number $q$, the number $q / (1 - aq - bq^2)$ is an integer if and only if
$q = F_i(1) / F_{i+1}(1)$ for some $i \in \mathbb{N}$ or $q = -F_{i+1}(1) / (b F_i(1))$ for some
$i \ge 1$.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024, Theorem 1.4
(`fq-2024-tsuno05142024-thm-1.4`). -/
public theorem_wanted fibonacciGenFun_eval_isInt_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hba : b ∣ a) (q : ℚ) :
    (∃ n : ℤ, q / (1 - a * q - b * q ^ 2) = n) ↔
      (∃ i : ℕ, q = (((𝔽[a, b] i).eval 1 : ℤ) : ℚ) / (((𝔽[a, b] (i + 1)).eval 1 : ℤ) : ℚ)) ∨
        ∃ i : ℕ, 0 < i ∧
          q = -(((𝔽[a, b] (i + 1)).eval 1 : ℤ) : ℚ) / (b * (((𝔽[a, b] i).eval 1 : ℤ) : ℚ))

/-- **Integer values of the generalized Lucas generating function at rationals.** Let $a$ and $b$
be positive integers with $b \mid a$, and let $F_i(x), L_i(x) \in \mathbb{Z}[x]$ be the
polynomials with $F_0 = 0$, $F_1 = 1$, $L_0 = 2$, $L_1 = ax$ and
$G_{i+2} = ax\,G_{i+1} + b\,G_i$ for $G = F, L$ and all $i \ge 0$. For a rational number $q$, the
number $(2 - aq) / (1 - aq - bq^2)$ is an integer if and only if $q$ is one of
$F_i(1) / F_{i+1}(1)$, $L_i(1) / L_{i+1}(1)$ and $-L_{i+1}(1) / (b L_i(1))$ for some
$i \in \mathbb{N}$, or $q = -F_{i+1}(1) / (b F_i(1))$ for some $i \ge 1$.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024, Theorem 1.5
(`fq-2024-tsuno05142024-thm-1.5`). -/
public theorem_wanted lucasGenFun_eval_isInt_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hba : b ∣ a) (q : ℚ) :
    (∃ n : ℤ, (2 - a * q) / (1 - a * q - b * q ^ 2) = n) ↔
      (∃ i : ℕ, q = (((𝔽[a, b] i).eval 1 : ℤ) : ℚ) / (((𝔽[a, b] (i + 1)).eval 1 : ℤ) : ℚ) ∨
          q = (((𝕃[a, b] i).eval 1 : ℤ) : ℚ) / (((𝕃[a, b] (i + 1)).eval 1 : ℤ) : ℚ) ∨
          q = -(((𝕃[a, b] (i + 1)).eval 1 : ℤ) : ℚ) / (b * (((𝕃[a, b] i).eval 1 : ℤ) : ℚ))) ∨
        ∃ i : ℕ, 0 < i ∧
          q = -(((𝔽[a, b] (i + 1)).eval 1 : ℤ) : ℚ) / (b * (((𝔽[a, b] i).eval 1 : ℤ) : ℚ))

/-- **Integer values of the generalized Fibonacci generating function in its interval of
convergence.** Let $a$ and $b$ be positive integers with $b \mid a$, and let
$F_i(x) \in \mathbb{Z}[x]$ be the polynomials with $F_0 = 0$, $F_1 = 1$ and
$F_{i+2} = ax\,F_{i+1} + b\,F_i$ for all $i \ge 0$. For a rational number $q$ with
$|q| < 2 / (a + \sqrt{a^2 + 4b})$, the radius of convergence of the power series of
$t / (1 - at - bt^2)$, the number $q / (1 - aq - bq^2)$ is an integer if and only if
$q = F_{2i}(1) / F_{2i+1}(1)$ for some $i \in \mathbb{N}$.

The source attributes this result (its Theorem 1.1) to Bulawa and Lee.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024, Corollary 1.6
(`fq-2024-tsuno05142024-cor-1.6`) and Theorem 1.1 (`fq-2024-tsuno05142024-thm-1.1`). -/
public theorem_wanted fibonacciGenFun_eval_isInt_iff_of_abs_lt_radius {a b : ℕ} (ha : 0 < a)
    (hb : 0 < b) (hba : b ∣ a) {q : ℚ}
    (hq : |(q : ℝ)| < 2 / (a + Real.sqrt (a ^ 2 + 4 * b))) :
    (∃ n : ℤ, q / (1 - a * q - b * q ^ 2) = n) ↔
      ∃ i : ℕ, q = (((𝔽[a, b] (2 * i)).eval 1 : ℤ) : ℚ) / (((𝔽[a, b] (2 * i + 1)).eval 1 : ℤ) : ℚ)

/-- **Integer values of the generalized Lucas generating function in its interval of
convergence.** Let $a$ and $b$ be positive integers with $a \ne 1$ and $b \mid a$, and let
$F_i(x), L_i(x) \in \mathbb{Z}[x]$ be the polynomials with $F_0 = 0$, $F_1 = 1$, $L_0 = 2$,
$L_1 = ax$ and $G_{i+2} = ax\,G_{i+1} + b\,G_i$ for $G = F, L$ and all $i \ge 0$. For a rational
number $q$ with $|q| < 2 / (a + \sqrt{a^2 + 4b})$, the radius of convergence of the power series
of $(2 - at) / (1 - at - bt^2)$, the number $(2 - aq) / (1 - aq - bq^2)$ is an integer if and
only if $q = F_{2i}(1) / F_{2i+1}(1)$ or $q = L_{2i+1}(1) / L_{2i+2}(1)$ for some
$i \in \mathbb{N}$.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024, Corollary 1.7
(`fq-2024-tsuno05142024-cor-1.7`). -/
public theorem_wanted lucasGenFun_eval_isInt_iff_of_abs_lt_radius {a b : ℕ} (ha : 0 < a)
    (ha1 : a ≠ 1) (hb : 0 < b) (hba : b ∣ a) {q : ℚ}
    (hq : |(q : ℝ)| < 2 / (a + Real.sqrt (a ^ 2 + 4 * b))) :
    (∃ n : ℤ, (2 - a * q) / (1 - a * q - b * q ^ 2) = n) ↔
      ∃ i : ℕ, q = (((𝔽[a, b] (2 * i)).eval 1 : ℤ) : ℚ) / (((𝔽[a, b] (2 * i + 1)).eval 1 : ℤ) : ℚ) ∨
        q = (((𝕃[a, b] (2 * i + 1)).eval 1 : ℤ) : ℚ) / (((𝕃[a, b] (2 * i + 2)).eval 1 : ℤ) : ℚ)

/-- **Integer values of the Lucas number generating function in its interval of convergence.**
Let $F_n$ be the Fibonacci numbers and $L_n$ the Lucas numbers, given by $L_0 = 2$, $L_1 = 1$
and $L_{n+2} = L_{n+1} + L_n$. For a rational number $q$ with $|q| < 2 / (1 + \sqrt 5)$, the
number $(2 - q) / (1 - q - q^2)$ is an integer if and only if $q = -1/2$, or
$q = F_{2i} / F_{2i+1}$ or $q = L_{2i+1} / L_{2i+2}$ for some $i \in \mathbb{N}$.

This is the case $a = b = 1$ of the generating function $(2 - at) / (1 - at - bt^2)$.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024, Corollary 1.8
(`fq-2024-tsuno05142024-cor-1.8`). -/
public theorem_wanted lucasNumberGenFun_eval_isInt_iff_of_abs_lt_radius {q : ℚ}
    (hq : |(q : ℝ)| < 2 / (1 + Real.sqrt 5)) :
    (∃ n : ℤ, (2 - q) / (1 - q - q ^ 2) = n) ↔
      (∃ i : ℕ, q = (Nat.fib (2 * i) : ℚ) / Nat.fib (2 * i + 1) ∨
        q = (lucasNumber (2 * i + 1) : ℚ) / lucasNumber (2 * i + 2)) ∨ q = -1 / 2

/-- **Polynomial Pell-type solutions as rescaled Fibonacci–Lucas polynomials.** Let $a$ and $b$ be
positive integers, and let $F_n(x), L_n(x) \in \mathbb{Z}[x]$ be the polynomials with $F_0 = 0$,
$F_1 = 1$, $L_0 = 2$, $L_1 = ax$ and $G_{n+2} = ax\,G_{n+1} + b\,G_n$ for $G = F, L$ and all
$n \ge 0$. Let $r_0 \in \{0, 1\}$ and let $P(x), Q(x) \in \mathbb{Q}[x]$ have nonnegative leading
coefficients (the zero polynomial has leading coefficient $0$) and satisfy
$P(x)^2 - (a^2x^2 + 4b) Q(x)^2 = 4(-b)^{r_0}$. Then there is $n \in \mathbb{N}$ with
$n \equiv r_0 \pmod 2$, $b^{\lfloor n/2 \rfloor} P(x) = L_n(x)$ and
$b^{\lfloor n/2 \rfloor} Q(x) = F_n(x)$.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024,
Proposition 2.1 (`fq-2024-tsuno05142024-prop-2.1`). -/
public theorem_wanted fibLucasPoly_of_pell_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {P Q : ℚ[X]} (hP : 0 ≤ P.leadingCoeff) (hQ : 0 ≤ Q.leadingCoeff) {r₀ : ℕ} (hr₀ : r₀ ≤ 1)
    (h : P ^ 2 - (C ((a : ℚ) ^ 2) * X ^ 2 + C (4 * (b : ℚ))) * Q ^ 2 = C (4 * (-(b : ℚ)) ^ r₀)) :
    ∃ n : ℕ, C ((b : ℚ) ^ (n / 2)) * P = (𝕃[a, b] n).map (Int.castRingHom ℚ) ∧
      C ((b : ℚ) ^ (n / 2)) * Q = (𝔽[a, b] n).map (Int.castRingHom ℚ) ∧ n % 2 = r₀

/-- **Pell-type solutions as rescaled odd Fibonacci–Lucas values, squarefree case.** Let $a$ and
$b$ be positive integers with $b \mid a$ and $b$ squarefree, and let
$F_i(x), L_i(x) \in \mathbb{Z}[x]$ be the polynomials with $F_0 = 0$, $F_1 = 1$, $L_0 = 2$,
$L_1 = ax$ and $G_{i+2} = ax\,G_{i+1} + b\,G_i$ for $G = F, L$ and all $i \ge 0$. If natural
numbers $P$ and $Q$ satisfy $P^2 - (a^2 + 4b) Q^2 = -4b$, then there is $n \in \mathbb{N}$ with
$b^n P = L_{2n+1}(1)$ and $b^n Q = F_{2n+1}(1)$.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024,
Proposition 2.2 (`fq-2024-tsuno05142024-prop-2.2`). -/
public theorem_wanted fibLucas_odd_of_pell_eq_of_squarefree {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hba : b ∣ a) (hsq : Squarefree b) {P Q : ℕ}
    (h : (P : ℤ) ^ 2 - (a ^ 2 + 4 * b) * Q ^ 2 = -4 * b) :
    ∃ n : ℕ, (b : ℤ) ^ n * P = (𝕃[a, b] (2 * n + 1)).eval 1 ∧
      (b : ℤ) ^ n * Q = (𝔽[a, b] (2 * n + 1)).eval 1

/-- **Pell-type solutions as rescaled odd Fibonacci–Lucas values.** Let $a$ and $b$ be positive
integers with $b \mid a$, and let $F_i(x), L_i(x) \in \mathbb{Z}[x]$ be the polynomials with
$F_0 = 0$, $F_1 = 1$, $L_0 = 2$, $L_1 = ax$ and $G_{i+2} = ax\,G_{i+1} + b\,G_i$ for $G = F, L$
and all $i \ge 0$. If natural numbers $P$ and $Q$ satisfy $P^2 - (a^2 + 4b) Q^2 = -4b$, then
there is $n \in \mathbb{N}$ with $b^n P = L_{2n+1}(1)$ and $b^n Q = F_{2n+1}(1)$.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024,
Proposition 2.3 (`fq-2024-tsuno05142024-prop-2.3`). -/
public theorem_wanted fibLucas_odd_of_pell_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hba : b ∣ a)
    {P Q : ℕ} (h : (P : ℤ) ^ 2 - (a ^ 2 + 4 * b) * Q ^ 2 = -4 * b) :
    ∃ n : ℕ, (b : ℤ) ^ n * P = (𝕃[a, b] (2 * n + 1)).eval 1 ∧
      (b : ℤ) ^ n * Q = (𝔽[a, b] (2 * n + 1)).eval 1

end

end MetaMathlibExt
