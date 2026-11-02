/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- **When the absolute discriminant of a $k$-generalized Fibonacci polynomial is a
$k$-generalized Fibonacci number.** Let $k \ge 2$ be a natural number and let
$F : \mathbb{Z} \to \mathbb{Z}$ satisfy $F(n) = 0$ for every integer $n$ with
$2 - k \le n \le 0$, $F(1) = 1$, and $F(n) = F(n-1) + F(n-2) + \cdots + F(n-k)$ for every
integer $n \ge 2$, so that $F(n)$ for $n \ge 0$ is the $k$-generalized Fibonacci sequence. Then
the absolute value of the discriminant of the polynomial
$X^k - X^{k-1} - \cdots - X - 1 \in \mathbb{Z}[X]$ equals $F(n)$ for some natural number $n$ if
and only if $k = 2$ or $k = 3$.

For $k = 2$ the absolute value of the discriminant is $5 = F(5)$, and for $k = 3$ it is
$44 = F(8)$. The paper prints the target set as $\{F_n\}$; that it means the $k$-generalized
sequence follows from its Lemma 1 and from Batte and Luca's restatement of this theorem
(arXiv 2504.02514, Introduction). With the classical Fibonacci numbers the case $k = 3$ would
fail, since $44$ is not a Fibonacci number.

Source: Florian Luca, *On the Discriminant of the k-Generalized Fibonacci Polynomial, II*,
The Fibonacci Quarterly 62 (2024), no. 3, Theorem 1 (`fq-2024-luca02082024-thm-1`). -/
public theorem_wanted abs_discr_kGeneralizedFibonacciPolynomial_mem_iff (k : ℕ) (hk : 2 ≤ k)
    (F : ℤ → ℤ) (hFzero : ∀ n : ℤ, 2 - (k : ℤ) ≤ n → n < 1 → F n = 0) (hFone : F 1 = 1)
    (hFrec : ∀ n : ℤ, 1 < n → F n = ∑ i ∈ Finset.range k, F (n - 1 - (i : ℤ))) :
    (∃ n : ℕ, |(X ^ k - ∑ i ∈ Finset.range k, X ^ i : ℤ[X]).discr| = F n) ↔ k = 2 ∨ k = 3

/-- **Bounds on the index in Luca's discriminant equation.** Let $k > 100$ be a natural number
and let $F : \mathbb{Z} \to \mathbb{Z}$ satisfy $F(n) = 0$ for every integer $n$ with
$2 - k \le n \le 0$, $F(1) = 1$, and $F(n) = F(n-1) + F(n-2) + \cdots + F(n-k)$ for every
integer $n \ge 2$ (the $k$-generalized Fibonacci sequence). Write
$L = (k \log k - 2 \log(k-1)) / \log 2$, where $\log$ is the natural logarithm. If a natural
number $n$ satisfies $F(n)\,(k-1)^2 = 2^{k+1} k^k - (k+1)^{k+1}$, then
$k + 1.99 + L < n < k + 3.01 + L$.

The equation is the paper's equation (7),
$F(n) = (2^{k+1} k^k - (k+1)^{k+1}) / (k-1)^2$, multiplied by $(k-1)^2$.

Source: Florian Luca, *On the Discriminant of the k-Generalized Fibonacci Polynomial, II*,
The Fibonacci Quarterly 62 (2024), no. 3, Lemma 1 (`fq-2024-luca02082024-lem-1`). Equation (7) is written after
multiplying by `(k-1)^2`; `F^{(k)}` is given by its defining properties as in
`abs_discr_kGeneralizedFibonacciPolynomial_mem_iff`. By Theorem 1 the equation has no
solution with `k > 100`, so this intermediate bound is implied by that statement. -/
public theorem_wanted kGeneralizedFibonacci_discr_eq_index_bounds (k : ℕ) (hk : 100 < k)
    (F : ℤ → ℤ) (hFzero : ∀ n : ℤ, 2 - (k : ℤ) ≤ n → n < 1 → F n = 0) (hFone : F 1 = 1)
    (hFrec : ∀ n : ℤ, 1 < n → F n = ∑ i ∈ Finset.range k, F (n - 1 - (i : ℤ)))
    (n : ℕ)
    (h7 : F n * ((k : ℤ) - 1) ^ 2 = 2 ^ (k + 1) * (k : ℤ) ^ k - ((k : ℤ) + 1) ^ (k + 1)) :
    (k : ℝ) + 1.99 + ((k : ℝ) * Real.log k - 2 * Real.log ((k : ℝ) - 1)) / Real.log 2 <
        (n : ℝ) ∧
      (n : ℝ) < (k : ℝ) + 3.01 +
        ((k : ℝ) * Real.log k - 2 * Real.log ((k : ℝ) - 1)) / Real.log 2

/-- **Absolute bounds on solutions of Luca's discriminant equation.** Let $k > 100$ be a natural
number and let $F : \mathbb{Z} \to \mathbb{Z}$ satisfy $F(n) = 0$ for every integer $n$ with
$2 - k \le n \le 0$, $F(1) = 1$, and $F(n) = F(n-1) + F(n-2) + \cdots + F(n-k)$ for every
integer $n \ge 2$ (the $k$-generalized Fibonacci sequence). If a natural number $n$ satisfies
$F(n)\,(k-1)^2 = 2^{k+1} k^k - (k+1)^{k+1}$, then $k < 2 \cdot 10^{16}$ and
$n < 1.5 \cdot 10^{18}$.

The equation is the paper's equation (7) multiplied by $(k-1)^2$.

Source: Florian Luca, *On the Discriminant of the k-Generalized Fibonacci Polynomial, II*,
The Fibonacci Quarterly 62 (2024), no. 3, Lemma 2 (`fq-2024-luca02082024-lem-2`). Equation (7) is written after
multiplying by `(k-1)^2`, as in `kGeneralizedFibonacci_discr_eq_index_bounds`; by Theorem 1
the hypotheses are never met. -/
public theorem_wanted kGeneralizedFibonacci_discr_eq_bounds (k : ℕ) (hk : 100 < k)
    (F : ℤ → ℤ) (hFzero : ∀ n : ℤ, 2 - (k : ℤ) ≤ n → n < 1 → F n = 0) (hFone : F 1 = 1)
    (hFrec : ∀ n : ℤ, 1 < n → F n = ∑ i ∈ Finset.range k, F (n - 1 - (i : ℤ)))
    (n : ℕ)
    (h7 : F n * ((k : ℤ) - 1) ^ 2 = 2 ^ (k + 1) * (k : ℤ) ^ k - ((k : ℤ) + 1) ^ (k + 1)) :
    k < 2 * 10 ^ 16 ∧ 2 * n < 3 * 10 ^ 18

end

end MetaMathlibExt
