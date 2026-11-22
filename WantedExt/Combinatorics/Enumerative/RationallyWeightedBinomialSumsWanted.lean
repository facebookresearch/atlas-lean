/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.Harmonic.Defs
public import MathlibExt.Combinatorics.Enumerative.HsuShiueGeneralizedStirlingNumber
public import MathlibExt.NumberTheory.LucasSequence
import MathlibExt.Combinatorics.Enumerative.StirlingSecondExplicit

/-!
# Rationally weighted binomial sums via differential and integral operators

Statements from Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation
of Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), no. 1, 45–56.

`{r, i}` is `Nat.stirlingSecond r i`, `(N)_i` is the falling factorial `N.descFactorial i`, and the
rising factorial `(k + 1)^{(s)} = (k + 1)(k + 2) ⋯ (k + s)` is `(k + 1).ascFactorial s`. A
polynomial `f(x) = ∑_{k=0}^N a_k x^k` is written `∑ k ∈ range (N + 1), C (a k) * X ^ k`, and its
`i`-th derivative is `derivative^[i]`. `F_n` and `L_n` are `Nat.fib n` and `lucasNumber n`.
-/

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- **Scherk's identity.** Write $S(r, i)$ for the Stirling numbers of the second kind. Let $N$ and
$r$ be natural numbers, let $a_0, \dots, a_N$ be real numbers, and let $f$ be the polynomial
$f(y) = \sum_{k=0}^{N} a_k y^k$, with $i$-th derivative $f^{(i)}$. Then for every real number $x$,
with the convention $0^0 = 1$,
$$\sum_{k=0}^{N} k^r a_k x^k = \sum_{i=0}^{r} S(r, i) \, x^i f^{(i)}(x).$$

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 2.1, equation (2.1). -/
public theorem_wanted sum_pow_mul_coeff_eq_sum_stirlingSecond_derivative (a : ℕ → ℝ) (N r : ℕ)
    (x : ℝ) :
    ∑ k ∈ Finset.range (N + 1), (k : ℝ) ^ r * a k * x ^ k =
      ∑ i ∈ Finset.range (r + 1), (Nat.stirlingSecond r i : ℝ) * x ^ i *
        (derivative^[i] (∑ k ∈ Finset.range (N + 1), C (a k) * X ^ k)).eval x

/-- **Scherk's identity with $s$-rising factorials.** Let $s$ be a real number and let $S(n, k)$
be the generalized Stirling numbers of Hsu and Shiue with parameters $(-s, 1, 0)$: a real array
with $S(0, 0) = 1$, $S(n, 0) = 0$ for $n \ge 1$, $S(n, k) = 0$ for $n < k$, and
$S(n+1, k+1) = S(n, k) + (k + 1 + ns) \, S(n, k+1)$ for all $n, k \ge 0$. Let $N$ and $r$ be
natural numbers, let $a_0, \dots, a_N$ be real numbers, and let $f(y) = \sum_{k=0}^{N} a_k y^k$,
with $i$-th derivative $f^{(i)}$. Then for every real number $x > 0$,
$$\sum_{k=0}^{N} k (k + s) \cdots (k + (r-1)s) \, a_k x^{k + rs} =
\sum_{i=0}^{r} S(r, i) \, x^{rs + i} f^{(i)}(x),$$
where the product $k (k + s) \cdots (k + (r-1)s)$ has the $r$ factors $k + js$, $0 \le j < r$,
and is $1$ when $r = 0$.

The powers of $x$ have real exponents, which is why $x > 0$ is assumed.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 2.1, equation (2.2). -/
public theorem_wanted sum_risingStep_mul_coeff_eq_sum_hsuShiue_derivative (s : ℝ)
    (S : ℕ → ℕ → ℝ) (hS : IsHsuShiueFamily S (-s) 1 0) (a : ℕ → ℝ) (N r : ℕ) (x : ℝ)
    (hx : 0 < x) :
    ∑ k ∈ Finset.range (N + 1),
        (∏ j ∈ Finset.range r, ((k : ℝ) + j * s)) * a k * x ^ ((k : ℝ) + r * s) =
      ∑ i ∈ Finset.range (r + 1), S r i * x ^ ((r : ℝ) * s + i) *
        (derivative^[i] (∑ k ∈ Finset.range (N + 1), C (a k) * X ^ k)).eval x

/-- **Stirling numbers of the second kind with three blocks.** For every integer $r \ge 1$, the
Stirling number of the second kind $S(r, 3)$ satisfies
$S(r, 3) = \frac{3^{r-1} + 1}{2} - 2^{r-1}$.

The source states this for $r \ge 3$; both sides vanish at $r = 1$ and $r = 2$.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Proposition 2.2. -/
public theorem stirlingSecond_three_eq (r : ℕ) (hr : 1 ≤ r) :
    (Nat.stirlingSecond r 3 : ℚ) = (3 ^ (r - 1) + 1) / 2 - 2 ^ (r - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hr
  have h := stirlingSecond_mul_factorial_eq_sum (1 + m) 3
  simp [Finset.sum_range_succ, Nat.factorial, pow_add] at h
  have hR : ((Nat.stirlingSecond (1 + m) 3 : ℚ) : ℝ) = (((3 ^ m + 1) / 2 - 2 ^ m : ℚ) : ℝ) := by
    push_cast
    linear_combination h / 6
  rw [Nat.add_sub_cancel_left]
  exact_mod_cast hR

/-- **Greenstreet's identity.** For every natural number $N$,

$$\sum_{k=1}^{N} (-1)^k \binom{N}{k} 2^{N-k} k^2 = N^2 - 2N.$$

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 2.3. -/
public theorem_wanted sum_neg_one_pow_choose_two_pow_mul_sq (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (-1 : ℤ) ^ k * (N.choose k : ℤ) * 2 ^ (N - k) * (k : ℤ) ^ 2 =
      (N : ℤ) ^ 2 - 2 * N

/-- **Polynomially weighted Fibonacci sums via derivatives.** Let $F_n$ denote the Fibonacci
numbers and $S(r, i)$ the Stirling numbers of the second kind. Let $t$ and $N$ be natural numbers,
let $A_0, \dots, A_t$ be complex numbers, let $h(y) = \sum_{r=0}^{t} A_r y^r$, and let $P$ be the
polynomial $P(y) = \sum_{j=0}^{N} F_j y^j$, with $i$-th derivative $P^{(i)}$. Then for every
$x \in \mathbb{C}$,
$$\sum_{k=0}^{N} h(k) F_k x^k = \sum_{r=0}^{t} A_r \sum_{i=0}^{r} S(r, i) \, x^i P^{(i)}(x).$$

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 2.4. -/
public theorem_wanted sum_poly_mul_fib_pow_eq_sum_stirlingSecond_derivative (A : ℕ → ℂ)
    (t N : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (N + 1),
        (∑ r ∈ Finset.range (t + 1), A r * (k : ℂ) ^ r) * (Nat.fib k : ℂ) * x ^ k =
      ∑ r ∈ Finset.range (t + 1), A r * ∑ i ∈ Finset.range (r + 1),
        (Nat.stirlingSecond r i : ℂ) * x ^ i *
          (derivative^[i] (∑ j ∈ Finset.range (N + 1), C (Nat.fib j : ℂ) * X ^ j)).eval x

/-- **Power-weighted binomial sums of Fibonacci numbers.** Let $F_n$ denote the Fibonacci numbers,
$S(r, i)$ the Stirling numbers of the second kind and $(N)_i = N(N-1) \cdots (N-i+1)$ the falling
factorial, with $(N)_0 = 1$. For all natural numbers $N$ and $r$,
$$\sum_{k=0}^{N} k^r \binom{N}{k} F_k = \sum_{i=0}^{r} S(r, i) \, (N)_i \, F_{2N-i},$$
where the terms with $i > N$ vanish because $(N)_i = 0$.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 2.5. -/
public theorem_wanted sum_pow_mul_choose_mul_fib (N r : ℕ) :
    ∑ k ∈ Finset.range (N + 1), k ^ r * N.choose k * Nat.fib k =
      ∑ i ∈ Finset.range (r + 1), Nat.stirlingSecond r i * N.descFactorial i * Nat.fib (2 * N - i)

/-- **Power-weighted binomial sums of Lucas numbers.** Let $L_n$ denote the Lucas numbers
($L_0 = 2$, $L_1 = 1$, $L_{n+2} = L_{n+1} + L_n$), $S(r, i)$ the Stirling numbers of the second
kind and $(N)_i = N(N-1) \cdots (N-i+1)$ the falling factorial, with $(N)_0 = 1$. For all natural
numbers $N$ and $r$, with the convention $0^0 = 1$,
$$\sum_{k=0}^{N} k^r \binom{N}{k} L_k = \sum_{i=0}^{r} S(r, i) \, (N)_i \, L_{2N-i},$$
where the terms with $i > N$ vanish because $(N)_i = 0$.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 2.5. -/
public theorem_wanted sum_pow_mul_choose_mul_lucasNumber (N r : ℕ) :
    ∑ k ∈ Finset.range (N + 1), k ^ r * N.choose k * lucasNumber k =
      ∑ i ∈ Finset.range (r + 1),
        Nat.stirlingSecond r i * N.descFactorial i * lucasNumber (2 * N - i)

/-- **Power-weighted binomial sums of a second-order linear recurrence.** Let $a$ and $b$ be real
numbers and let $(W_n)_{n \ge 0}$ be a real sequence with $W_{n+2} = a W_{n+1} + b W_n$ for all
$n \ge 0$. Write $S(r, i)$ for the Stirling numbers of the second kind and
$(N)_i = N(N-1) \cdots (N-i+1)$ for the falling factorial, with $(N)_0 = 1$. Then for all natural
numbers $N$ and $r$, with the convention $0^0 = 1$,
$$\sum_{k=0}^{N} k^r \binom{N}{k} a^k b^{N-k} W_k = \sum_{i=0}^{r} S(r, i) (N)_i a^i W_{2N-i},$$
where the terms with $i > N$ vanish because $(N)_i = 0$.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 2.5. -/
public theorem_wanted sum_pow_mul_choose_mul_secondOrder (a b : ℝ) (W : ℕ → ℝ)
    (hW : ∀ n, W (n + 2) = a * W (n + 1) + b * W n) (N r : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (k : ℝ) ^ r * N.choose k * a ^ k * b ^ (N - k) * W k =
      ∑ i ∈ Finset.range (r + 1),
        (Nat.stirlingSecond r i : ℝ) * N.descFactorial i * a ^ i * W (2 * N - i)

/-- **Weighted binomial Fibonacci sums for the powers one to four.** Let $F_n$ denote the Fibonacci
numbers. For every natural number $N$,
$$\sum_{k=1}^{N} k \binom{N}{k} F_k = N F_{2N-1},$$
$$\sum_{k=1}^{N} k^2 \binom{N}{k} F_k = N F_{2N-1} + N(N-1) F_{2N-2},$$
$$\sum_{k=1}^{N} k^3 \binom{N}{k} F_k = N F_{2N-1} + 3N(N-1) F_{2N-2} + N(N-1)(N-2) F_{2N-3},$$
$$\sum_{k=1}^{N} k^4 \binom{N}{k} F_k = N F_{2N-1} + 7N(N-1) F_{2N-2} +
6N(N-1)(N-2) F_{2N-3} + N(N-1)(N-2)(N-3) F_{2N-4}.$$

Every term with a negative Fibonacci index has coefficient zero.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 2.6. -/
public theorem_wanted sum_pow_mul_choose_mul_fib_small (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, k * N.choose k * Nat.fib k = N * Nat.fib (2 * N - 1)) ∧
    (∑ k ∈ Finset.Icc 1 N, k ^ 2 * N.choose k * Nat.fib k =
      N * Nat.fib (2 * N - 1) + N * (N - 1) * Nat.fib (2 * N - 2)) ∧
    (∑ k ∈ Finset.Icc 1 N, k ^ 3 * N.choose k * Nat.fib k =
      N * Nat.fib (2 * N - 1) + 3 * N * (N - 1) * Nat.fib (2 * N - 2) +
        N * (N - 1) * (N - 2) * Nat.fib (2 * N - 3)) ∧
    ∑ k ∈ Finset.Icc 1 N, k ^ 4 * N.choose k * Nat.fib k =
      N * Nat.fib (2 * N - 1) + 7 * N * (N - 1) * Nat.fib (2 * N - 2) +
        6 * N * (N - 1) * (N - 2) * Nat.fib (2 * N - 3) +
        N * (N - 1) * (N - 2) * (N - 3) * Nat.fib (2 * N - 4)

/-- **Polynomially weighted binomial Fibonacci sums.** Let $F_n$ denote the Fibonacci numbers,
$S(j, i)$ the Stirling numbers of the second kind and $(N)_i = N(N-1)\cdots(N-i+1)$ the falling
factorial. Let $A_0, A_1, A_2, \dots$ be complex numbers and $N$, $t$ natural numbers, and put
$h(y) = \sum_{j=0}^{t} A_j y^j$. Then

$$\sum_{k=1}^{N} h(k) \binom{N}{k} F_k =
\sum_{j=0}^{t} A_j \sum_{i=0}^{j} S(j, i)\, (N)_i\, F_{2N-i}.$$

Moreover,
$\sum_{k=1}^{N} (A_0 + A_1 k + A_2 k^2 + A_3 k^3 + A_4 k^4) \binom{N}{k} F_k$ equals
$A_0 F_{2N} + (A_1 + A_2 + A_3 + A_4) \binom{N}{1} F_{2N-1} +
2(A_2 + 3A_3 + 7A_4) \binom{N}{2} F_{2N-2} + 6(A_3 + 6A_4) \binom{N}{3} F_{2N-3} +
24 A_4 \binom{N}{4} F_{2N-4}$.

The source's hypotheses $N, t > 0$ and $t \le N/2$ are not needed and are dropped.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 2.7. -/
public theorem_wanted sum_poly_mul_choose_mul_fib (A : ℕ → ℂ) (N t : ℕ) :
    (∑ k ∈ Finset.Icc 1 N,
        (∑ j ∈ Finset.range (t + 1), A j * (k : ℂ) ^ j) * N.choose k * Nat.fib k =
      ∑ j ∈ Finset.range (t + 1), A j * ∑ i ∈ Finset.range (j + 1),
        (Nat.stirlingSecond j i : ℂ) * N.descFactorial i * Nat.fib (2 * N - i)) ∧
    ∑ k ∈ Finset.Icc 1 N,
        (∑ j ∈ Finset.range 5, A j * (k : ℂ) ^ j) * N.choose k * Nat.fib k =
      A 0 * Nat.fib (2 * N) + (A 1 + A 2 + A 3 + A 4) * N.choose 1 * Nat.fib (2 * N - 1) +
        2 * (A 2 + 3 * A 3 + 7 * A 4) * N.choose 2 * Nat.fib (2 * N - 2) +
        6 * (A 3 + 6 * A 4) * N.choose 3 * Nat.fib (2 * N - 3) +
        24 * A 4 * N.choose 4 * Nat.fib (2 * N - 4)

/-- **Polynomially weighted binomial sums of powers of a second-order sequence.** Let $a$, $b$ be
real numbers and $(U_n)_{n \ge 0}$ a real sequence with $U_{n+2} = a U_{n+1} + b U_n$ for all $n$.
Let $\alpha \ne \beta$ be complex numbers with $\alpha + \beta = a$ and $\alpha\beta = -b$ (the
roots of $y^2 = ay + b$), and put $A = (U_1 - U_0\beta)/(\alpha - \beta)$ and
$B = (U_1 - U_0\alpha)/(\alpha - \beta)$. Let $S(j, i)$ denote the Stirling numbers of the second
kind and $(N)_i = N(N-1)\cdots(N-i+1)$ the falling factorial. Let $c_0, c_1, c_2, \dots$ be
complex numbers, $t$, $N$, $r$ natural numbers and $h(y) = \sum_{j=0}^{t} c_j y^j$. Then for every
complex number $x$,

$$\sum_{k=0}^{N} h(k) \binom{N}{k} U_k^r x^k =
\sum_{j=0}^{t} c_j \sum_{i=0}^{j} S(j, i)\, x^i \sum_{\ell=0}^{r} \binom{r}{\ell} A^\ell
(-B)^{r-\ell} (N)_i\, (\alpha^\ell \beta^{r-\ell})^i (1 + \alpha^\ell \beta^{r-\ell} x)^{N-i}.$$

The source prints $A^j$, with the outer index $j$, where its proof gives $A^\ell$; the printed
form fails for the Fibonacci numbers $U_k = F_k$, $h = 1$, $r = N = 1$, $x = 0$ (left side $0$,
printed right side $1 - 1/\sqrt{5}$). The source's coefficients $A_j$ of $h$ are renamed $c_j$,
and positivity of $r$, $N$, $t$ is dropped.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 2.8. -/
public theorem_wanted sum_poly_mul_choose_mul_secondOrder_pow (a b : ℝ) (U : ℕ → ℝ)
    (hU : ∀ n, U (n + 2) = a * U (n + 1) + b * U n) (α β : ℂ) (hαβ : α ≠ β)
    (hsum : α + β = a) (hprod : α * β = -b) (c : ℕ → ℂ) (t N r : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (N + 1),
        (∑ j ∈ Finset.range (t + 1), c j * (k : ℂ) ^ j) * N.choose k * (U k : ℂ) ^ r * x ^ k =
      ∑ j ∈ Finset.range (t + 1), c j * ∑ i ∈ Finset.range (j + 1),
        (Nat.stirlingSecond j i : ℂ) * x ^ i * ∑ l ∈ Finset.range (r + 1),
          (r.choose l : ℂ) * ((U 1 - U 0 * β) / (α - β)) ^ l *
            (-((U 1 - U 0 * α) / (α - β))) ^ (r - l) * N.descFactorial i *
            (α ^ l * β ^ (r - l)) ^ i * (1 + α ^ l * β ^ (r - l) * x) ^ (N - i)

/-- **Binomial sums with rising-factorial denominators.** Write $m^{(i)} = m(m+1)\cdots(m+i-1)$
for the rising factorial. For all natural numbers $N$ and $s \ge 1$ and every real number $x$,

$$\sum_{k=0}^{N} \binom{N}{k} \frac{x^{k+s}}{(k+1)^{(s)}} =
\frac{(1+x)^{N+s} - 1}{(N+1)^{(s)}} - \sum_{j=1}^{s-1} \frac{x^j}{j!\,(N+1)^{(s-j)}}.$$

The source writes $\binom{n}{k}$ for $\binom{N}{k}$.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 3.1, equation (3.1). -/
public theorem_wanted sum_choose_mul_pow_div_ascFactorial (N s : ℕ) (hs : 0 < s) (x : ℝ) :
    ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * x ^ (k + s) / (k + 1).ascFactorial s =
      ((1 + x) ^ (N + s) - 1) / (N + 1).ascFactorial s -
        ∑ j ∈ Finset.Icc 1 (s - 1), x ^ j / (j.factorial * (N + 1).ascFactorial (s - j))

/-- **Rising-factorial weighted sums via iterated antiderivatives.** Let $N$ and $s$ be natural
numbers, $a_0, \dots, a_N$ real numbers and $f(y) = \sum_{k=0}^{N} a_k y^k$. Let
$I_0, I_1, I_2, \dots$ be functions $\mathbb{R} \to \mathbb{R}$ with $I_0 = f$ such that for every
$j \ge 0$ the function $I_{j+1}$ is differentiable on $\mathbb{R}$ with derivative $I_j$ (the
constants of integration are arbitrary). Write $m^{(i)} = m(m+1)\cdots(m+i-1)$ for the rising
factorial. Then for every real number $x$,

$$\sum_{k=0}^{N} \frac{a_k\, x^{k+s}}{(k+1)^{(s)}} =
I_s(x) - \sum_{j=1}^{s} \frac{I_j(0)\, x^{s-j}}{(s-j)!}.$$

The source assumes $s > 0$; for $s = 0$ the identity reads $f(x) = I_0(x)$.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 3.1, equation (3.2). -/
public theorem_wanted sum_coeff_mul_pow_div_ascFactorial_eq_antideriv (a : ℕ → ℝ) (N s : ℕ)
    (I : ℕ → ℝ → ℝ) (hI0 : ∀ y, I 0 y = ∑ k ∈ Finset.range (N + 1), a k * y ^ k)
    (hI : ∀ j y, HasDerivAt (I (j + 1)) (I j y) y) (x : ℝ) :
    ∑ k ∈ Finset.range (N + 1), a k * x ^ (k + s) / (k + 1).ascFactorial s =
      I s x - ∑ j ∈ Finset.Icc 1 s, I j 0 * x ^ (s - j) / (s - j).factorial

/-- **Epsteen's identity.** For every natural number $n$,

$$\sum_{k=0}^{n} \frac{1}{k+1} \binom{n}{k} = \frac{2^{n+1} - 1}{n+1}.$$

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 3.2. -/
public theorem_wanted sum_choose_div_succ (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) / (k + 1) = (2 ^ (n + 1) - 1) / (n + 1)

/-- **Finkel's identity.** For every natural number $n$, with $H_n = \sum_{j=1}^{n} 1/j$ the
$n$-th harmonic number,

$$\sum_{k=1}^{n} (-1)^{k-1} \frac{1}{k} \binom{n}{k} = H_n.$$

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 3.2. -/
public theorem_wanted sum_neg_one_pow_choose_div_eq_harmonic (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (-1 : ℚ) ^ (k - 1) * n.choose k / k = harmonic n

/-- **Binomial sums weighted by $x^k/k^2$.** For every natural number $n$ and every real number
$x$,

$$\sum_{k=1}^{n} \binom{n}{k} \frac{x^k}{k^2} =
\sum_{k=1}^{n} \frac{1}{k} \sum_{j=1}^{k} \frac{(1+x)^j}{j} -
\sum_{k=1}^{n} \frac{1}{k} \sum_{j=1}^{k} \frac{1}{j}.$$

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 3.2. -/
public theorem_wanted sum_choose_mul_pow_div_sq (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.Icc 1 n, (n.choose k : ℝ) * x ^ k / (k : ℝ) ^ 2 =
      ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) * ∑ j ∈ Finset.Icc 1 k, (1 + x) ^ j / j -
        ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) * ∑ j ∈ Finset.Icc 1 k, 1 / (j : ℝ)

/-- **Alternating binomial sum with inverse-square weights.** For every natural number $n$, with
$H_k = \sum_{j=1}^{k} 1/j$ the $k$-th harmonic number,

$$\sum_{k=1}^{n} (-1)^{k-1} \frac{1}{k^2} \binom{n}{k} = \sum_{k=1}^{n} \frac{H_k}{k}.$$

This is the case $x = -1$ of identity (3.6) of the source.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 3.2. -/
public theorem_wanted sum_neg_one_pow_choose_div_sq_eq_sum_harmonic (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2 =
      ∑ k ∈ Finset.Icc 1 n, harmonic k / k

end

end MetaMathlibExt
