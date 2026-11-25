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
public import Mathlib.NumberTheory.Real.Irrational

namespace MetaMathlibExt

@[expose] public section

/-- **Products of two $k$-Fibonacci numbers that are repdigits.** Let $k \ge 3$ and let
$(F_n)_{n \ge 2-k}$ be the $k$-generalized Fibonacci sequence, given by
$F_{2-k} = \dots = F_0 = 0$, $F_1 = 1$ and $F_n = F_{n-1} + F_{n-2} + \dots + F_{n-k}$
for $n \ge 2$. Let $a, \ell, m, n$ be natural numbers with $3 \le m \le n$, $\ell \ge 2$ and
$1 \le a \le 9$. Then $F_n F_m = a (10^\ell - 1)/9$ (the $\ell$-digit repdigit with digit $a$)
if and only if $(a, k, \ell, m, n) = (8, 3, 2, 3, 8)$; indeed $F_8 F_3 = 44 \cdot 2 = 88$ for
$k = 3$.

Source: Safia Seffah, Salah Eddine Rihane, and Alain Togbé, *On an Equation
Involving Repdigits and Products of Two k-Fibonacci Numbers*, INTEGERS 25 (2025),
Article A55, Theorem 1 (`integers-2025-A55-thm-1`). -/
public theorem_wanted kFibonacci_mul_eq_repdigit_iff (k : ℕ) (hk : 3 ≤ k) (F : ℤ → ℤ)
    (hFzero : ∀ n : ℤ, 2 - (k : ℤ) ≤ n → n < 1 → F n = 0) (hFone : F 1 = 1)
    (hFrec : ∀ n : ℤ, 1 < n → F n = ∑ i ∈ Finset.range k, F (n - 1 - (i : ℤ)))
    {a ℓ m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hℓ : 2 ≤ ℓ) (ha : 1 ≤ a) (ha9 : a ≤ 9) :
    9 * (F n * F m) = a * (10 ^ ℓ - 1) ↔ (a, k, ℓ, m, n) = (8, 3, 2, 3, 8)

/-- **Index bound for repdigit products of $k$-Fibonacci numbers.** Let $k \ge 3$ and let
$(F_n)_{n \ge 2-k}$ be the $k$-generalized Fibonacci sequence, given by
$F_{2-k} = \dots = F_0 = 0$, $F_1 = 1$ and $F_n = F_{n-1} + F_{n-2} + \dots + F_{n-k}$
for $n \ge 2$. Let $a, \ell, m, n$ be natural numbers with $3 \le m \le n$, $\ell \ge 2$,
$1 \le a \le 9$ and $n \ge k + 2$. If $F_n F_m = a (10^\ell - 1)/9$, then
$n < 1.64 \cdot 10^{29} k^8 (\log k)^5$, where $\log$ is the natural logarithm.

Source: Safia Seffah, Salah Eddine Rihane, and Alain Togbé, *On an Equation
Involving Repdigits and Products of Two k-Fibonacci Numbers*, INTEGERS 25 (2025),
Article A55, Lemma 5 (`integers-2025-A55-lem-5`). -/
public theorem_wanted kFibonacci_repdigit_index_lt (k : ℕ) (hk : 3 ≤ k) (F : ℤ → ℤ)
    (hFzero : ∀ n : ℤ, 2 - (k : ℤ) ≤ n → n < 1 → F n = 0) (hFone : F 1 = 1)
    (hFrec : ∀ n : ℤ, 1 < n → F n = ∑ i ∈ Finset.range k, F (n - 1 - (i : ℤ)))
    {a ℓ m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hℓ : 2 ≤ ℓ) (ha : 1 ≤ a) (ha9 : a ≤ 9)
    (hkn : k + 2 ≤ n) (hsol : 9 * (F n * F m) = a * (10 ^ ℓ - 1)) :
    (n : ℝ) < 1.64e29 * (k : ℝ) ^ 8 * Real.log k ^ 5

/-- **Partial-quotient lower bound for rational approximation.** Let $\gamma$ be an irrational real
number with continued fraction $[a_0; a_1, a_2, \dots]$, so that $a_0 = \lfloor \gamma \rfloor$,
and let $q_0 = 1, q_1, q_2, \dots$ be the denominators of its convergents. Let $M \ge 1$ and
$N \ge 0$ be integers with $q_N \le M < q_{N+1}$, and let $A$ be a real number with $a_i \le A$
for $0 \le i \le N + 1$. Then $|x \gamma - y| > 1/((A + 2) x)$ for all integers $x, y$ with
$0 < x < M$.

Taking $A = \max(a_0, \dots, a_{N+1})$ gives the strongest bound.

Source: Safia Seffah, Salah Eddine Rihane, and Alain Togbé, *On an Equation
Involving Repdigits and Products of Two k-Fibonacci Numbers*, INTEGERS 25 (2025),
Article A55, Lemma 2 (`integers-2025-A55-lem-2`). -/
public theorem_wanted one_div_partialQuotient_bound_mul_lt_abs_mul_sub {γ : ℝ}
    (hγ : Irrational γ) {M N : ℕ} (hM : 0 < M) (hNM : (GenContFract.of γ).dens N ≤ M)
    (hMN : (M : ℝ) < (GenContFract.of γ).dens (N + 1)) {aL : ℝ} (ha0 : (⌊γ⌋ : ℝ) ≤ aL)
    (ha : ∀ j ≤ N, ∀ b : ℝ, (GenContFract.of γ).partDens.get? j = some b → b ≤ aL)
    {x y : ℤ} (hx : 0 < x) (hxM : x < M) :
    1 / ((aL + 2) * x) < |x * γ - y|

end

end MetaMathlibExt
