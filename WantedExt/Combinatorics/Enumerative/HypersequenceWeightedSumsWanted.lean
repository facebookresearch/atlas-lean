/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.Binomial
public import MathlibExt.NumberTheory.LucasSequence
public import WantedExt.NumberTheory.HyperLeonardoWanted

/-!
# Hypersequences of an arbitrary sequence and their weighted sums (Parisse)

Statements from Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their
Weighted Sums*, INTEGERS 24 (2024), Article A70.

Conventions. The hypersequence `a^{(r)}_n` is `hypersequence a r n`; the hyperfibonacci numbers
are the existing `hyperFibonacci` (bridge `hyperFibonacci_eq_hypersequence`), the Lucas numbers
are `lucasNumber` and the hyperlucas numbers are `hypersequence lucasNumber`. The paper's
sequences are complex; general statements use `ℂ`. `p_{ℓ,m}(x, y)` is
`alternatingBinomialPowerSum ℓ m x y`, and `c_{ℓ,m}(n) = p_{ℓ,m}(1, n + 1)`. `S(j, m)` is
`Nat.stirlingSecond`. The weighted sums `t^{(r)}_ℓ(n) = ∑_{k=0}^{n} k^ℓ a^{(r)}_k` are written
out (with `0^0 = 1`, as in the paper). Binomial coefficients `C(x, k)` with a possibly negative
upper argument are `Ring.choose` over `ℤ`.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- **Hypersequence.** Let $(a_n)_{n \ge 0}$ be a sequence in an additive commutative monoid.
Its hypersequence of generation $r$, written $a^{(r)}_n$, is defined by recursion on $r$:
$a^{(0)}_n = a_n$ and $a^{(r+1)}_n = \sum_{k=0}^{n} a^{(r)}_k$ for all natural numbers $r$ and
$n$. Thus each generation is the sequence of partial sums of the previous one.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Section 1, Equation (1.1). -/
public def hypersequence {R : Type*} [AddCommMonoid R] (a : ℕ → R) : ℕ → ℕ → R
  | 0, n => a n
  | r + 1, n => ∑ k ∈ range (n + 1), hypersequence a r k

/-- **Each hypersequence generation sums the previous one.** Let $(a_n)$ be a sequence in an
additive commutative monoid and let $a^{(r)}_n$ denote its hypersequence of generation $r$. For
all natural numbers $r$ and $n$, $a^{(r+1)}_n = \sum_{k=0}^{n} a^{(r)}_k$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Section 1, Equation (1.1). -/
public theorem hypersequence_succ {R : Type*} [AddCommMonoid R] (a : ℕ → R) (r n : ℕ) :
    hypersequence a (r + 1) n = ∑ k ∈ range (n + 1), hypersequence a r k :=
  rfl

/-- **First hypersequence at index zero.** Let $(a_n)$ be a sequence in an additive commutative
monoid and let $a^{(1)}_n$ denote its hypersequence of generation $1$. Then $a^{(1)}_0 = a_0$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Section 1, Equation (1.1). -/
public theorem hypersequence_one_zero {R : Type*} [AddCommMonoid R] (a : ℕ → R) :
    hypersequence a 1 0 = a 0 := by
  simp [hypersequence]

/-- **Hyperfibonacci numbers are the hypersequences of the Fibonacci numbers.** Let $F_k$ denote
the $k$th Fibonacci number. For all natural numbers $r$ and $n$, the hyperfibonacci number
$F^{(r)}_n$ equals the $r$th hypersequence of the Fibonacci sequence at $n$, that is,
$F^{(r)}_n = a^{(r)}_n$ for $a_k = F_k$, where $a^{(0)}_n = a_n$ and
$a^{(r+1)}_n = \sum_{k=0}^{n} a^{(r)}_k$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Example 3 (hyperfibonacci numbers). -/
public theorem hyperFibonacci_eq_hypersequence (r n : ℕ) :
    hyperFibonacci r n = hypersequence Nat.fib r n := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih => simp [hyperFibonacci, hypersequence, ih]

/-- **Alternating binomial power sum.** For natural numbers $\ell, m$ and complex numbers $x, y$,
$$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (kx + y)^\ell,$$
with the convention $0^0 = 1$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Section 3, Equation (3.9). -/
public def alternatingBinomialPowerSum (ℓ m : ℕ) (x y : ℂ) : ℂ :=
  ∑ k ∈ range (m + 1), (-1) ^ k * (m.choose k : ℂ) * (k * x + y) ^ ℓ

/-- **A value of the alternating binomial power sum.** The alternating binomial power sum
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (kx + y)^\ell$ satisfies
$p_{1,1}(1, 1) = 1 - 2 = -1$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Section 3, Equation (3.9). -/
public theorem alternatingBinomialPowerSum_one_one_one_one :
    alternatingBinomialPowerSum 1 1 1 1 = -1 := by
  simp [alternatingBinomialPowerSum, sum_range_succ]

/-- **Hypersequences as binomial sums.** Let $(a_n)$ be a sequence of complex numbers and let
$a^{(r)}_n$ denote its hypersequence of generation $r$. For every $r \ge 1$ and every natural
number $n$,
$$a^{(r)}_n = \sum_{k=0}^{n} \binom{n+r-1-k}{r-1} a_k = \sum_{k=0}^{n} \binom{r+k-1}{k} a_{n-k}.$$

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 1, Equation (2.1) (`integers-2024-A70-thm-1`). -/
public theorem_wanted hypersequence_eq_sum_choose (a : ℕ → ℂ) {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    hypersequence a r n = ∑ k ∈ range (n + 1), ((n + r - 1 - k).choose (r - 1) : ℂ) * a k ∧
      hypersequence a r n = ∑ k ∈ range (n + 1), ((r + k - 1).choose k : ℂ) * a (n - k)

/-- **Recurrence between consecutive hypersequence generations.** Let $(a_n)$ be a sequence of
complex numbers and let $a^{(r)}_n$ denote its hypersequence of generation $r$. For all natural
numbers $r$ and $n$, $a^{(r+1)}_{n+1} = a^{(r+1)}_n + a^{(r)}_{n+1}$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 2, Equation (2.2) (`integers-2024-A70-thm-2`). -/
public theorem_wanted hypersequence_succ_succ (a : ℕ → ℂ) (r n : ℕ) :
    hypersequence a (r + 1) (n + 1) = hypersequence a (r + 1) n + hypersequence a r (n + 1)

/-- **Hyperfibonacci numbers in terms of Fibonacci numbers.** Let $F_k$ denote the $k$th Fibonacci
number and $F^{(r)}_n$ the hyperfibonacci numbers, given by $F^{(0)}_n = F_n$ and
$F^{(r+1)}_n = \sum_{k=0}^{n} F^{(r)}_k$. For all natural numbers $r$ and $n$,
$$F^{(r)}_n = F_{n+2r} - \sum_{k=0}^{r-1} \binom{n + k - 1}{k} F_{2(r-k)}.$$

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 3, Equation (2.8) (`integers-2024-A70-thm-3`). -/
public theorem_wanted hyperFibonacci_eq_fib_sub_sum (r n : ℕ) :
    (hyperFibonacci r n : ℤ) =
      Nat.fib (n + 2 * r) - ∑ k ∈ range r, ((n + k - 1).choose k * Nat.fib (2 * (r - k)) : ℕ)

/-- **Fibonacci numbers as binomially weighted sums.** Let $F_k$ denote the $k$th Fibonacci
number. For every natural number $r \ge 1$ and every natural number $n$,
$$F_{n+2r} = \sum_{k=0}^{n} \binom{n + r - 1 - k}{r - 1} F_k +
\sum_{k=0}^{r-1} \binom{n + k - 1}{k} F_{2(r-k)}$$
and
$$F_{n+2r} = \sum_{k=0}^{n} \binom{r + k - 1}{k} F_{n-k} +
\sum_{k=0}^{r-1} \binom{n + k - 1}{k} F_{2(r-k)}.$$

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Corollary 1 (`integers-2024-A70-cor-1`). -/
public theorem_wanted fib_add_two_mul_eq_sum_choose {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    Nat.fib (n + 2 * r) = ∑ k ∈ range (n + 1), (n + r - 1 - k).choose (r - 1) * Nat.fib k +
        ∑ k ∈ range r, (n + k - 1).choose k * Nat.fib (2 * (r - k)) ∧
      Nat.fib (n + 2 * r) = ∑ k ∈ range (n + 1), (r + k - 1).choose k * Nat.fib (n - k) +
        ∑ k ∈ range r, (n + k - 1).choose k * Nat.fib (2 * (r - k))

/-- **Recurrence for the hyperfibonacci numbers.** Let $F^{(r)}_n$ denote the hyperfibonacci
numbers. For all natural numbers $r$ and $n$, $F^{(r)}_0 = 0$, $F^{(r)}_1 = 1$, and
$F^{(r+1)}_{n+2} = F^{(r+1)}_{n+1} + F^{(r+1)}_n + \binom{n+r+1}{r}$.

Equivalently, for $r \ge 1$, $F^{(r)}_{n+2} = F^{(r)}_{n+1} + F^{(r)}_n + \binom{n+r}{r-1}$, the
form in which Parisse quotes this result of Cristea, Martinjak and Urbiha.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 4, Equation (2.9) (`integers-2024-A70-thm-4`). -/
public theorem_wanted hyperFibonacci_recurrence (r n : ℕ) :
    hyperFibonacci r 0 = 0 ∧ hyperFibonacci r 1 = 1 ∧
      hyperFibonacci (r + 1) (n + 2) =
        hyperFibonacci (r + 1) (n + 1) + hyperFibonacci (r + 1) n + (n + r + 1).choose r

/-- **Hyperlucas numbers in terms of Lucas numbers.** Let $L_n$ denote the Lucas numbers and
let $L^{(r)}_n$ denote the hyperlucas numbers, the hypersequence of generation $r$ of $(L_n)$.
For all natural numbers $r$ and $n$, in the integers,
$$L^{(r)}_n = L_{n+2r} - \sum_{k=0}^{r-1} \binom{n+k}{k} L_{2(r-k)-1}.$$

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 5, Equation (2.12) (`integers-2024-A70-thm-5`). -/
public theorem_wanted hyperLucas_eq_lucas_sub_sum (r n : ℕ) :
    ((hypersequence lucasNumber r n : ℕ) : ℤ) =
      lucasNumber (n + 2 * r) -
        ∑ k ∈ range r, ((n + k).choose k * lucasNumber (2 * (r - k) - 1) : ℕ)

/-- **Lucas numbers as binomial sums.** Let $L_n$ denote the Lucas numbers. For every $r \ge 1$
and every natural number $n$,
$$L_{n+2r} = \sum_{k=0}^{n} \binom{n+r-1-k}{r-1} L_k +
\sum_{k=0}^{r-1} \binom{n+k}{k} L_{2(r-k)-1}$$
and
$$L_{n+2r} = \sum_{k=0}^{n} \binom{r+k-1}{k} L_{n-k} +
\sum_{k=0}^{r-1} \binom{n+k}{k} L_{2(r-k)-1}.$$

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Corollary 2 (`integers-2024-A70-cor-2`). -/
public theorem_wanted lucas_add_two_mul_eq_sum_choose {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    lucasNumber (n + 2 * r) =
        ∑ k ∈ range (n + 1), (n + r - 1 - k).choose (r - 1) * lucasNumber k +
          ∑ k ∈ range r, (n + k).choose k * lucasNumber (2 * (r - k) - 1) ∧
      lucasNumber (n + 2 * r) =
        ∑ k ∈ range (n + 1), (r + k - 1).choose k * lucasNumber (n - k) +
          ∑ k ∈ range r, (n + k).choose k * lucasNumber (2 * (r - k) - 1)

/-- **Recurrence for the hyperlucas numbers.** Let $L^{(r)}_n$ denote the hyperlucas numbers,
the hypersequence of generation $r$ of the Lucas numbers. For all natural numbers $r$ and $n$,
$L^{(r)}_0 = 2$, $L^{(r)}_1 = 2r + 1$, and, in the rational numbers,
$$L^{(r+1)}_{n+2} = L^{(r+1)}_{n+1} + L^{(r+1)}_n + \frac{n + 2(r+1)}{n+2} \binom{n+r+1}{r}.$$

Equivalently, for $r \ge 1$,
$$L^{(r)}_{n+2} = L^{(r)}_{n+1} + L^{(r)}_n + \frac{n+2r}{n+2} \binom{n+r}{r-1}.$$

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 6, Equation (2.13) (`integers-2024-A70-thm-6`). -/
public theorem_wanted hyperLucas_recurrence (r n : ℕ) :
    hypersequence lucasNumber r 0 = 2 ∧ hypersequence lucasNumber r 1 = 2 * r + 1 ∧
      ((hypersequence lucasNumber (r + 1) (n + 2) : ℕ) : ℚ) =
        ((hypersequence lucasNumber (r + 1) (n + 1) : ℕ) : ℚ) +
          ((hypersequence lucasNumber (r + 1) n : ℕ) : ℚ) +
          ((n + 2 * (r + 1) : ℕ) : ℚ) / (n + 2) * ((n + r + 1).choose r : ℚ)

/-- **Abel summation by parts.** Let $a$ and $b$ be sequences of complex numbers and let
$a^{(1)}_k = \sum_{i=0}^{k} a_i$ be the first hypersequence (the partial sums) of $a$. Then for
every natural number $n$,
$$\sum_{k=0}^{n} a_k b_k = a^{(1)}_n b_{n+1} + \sum_{k=0}^{n} a^{(1)}_k (b_k - b_{k+1}).$$

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 7 (`integers-2024-A70-thm-7`). -/
public theorem_wanted sum_mul_eq_hypersequence_one_mul_add_sum (a b : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ range (n + 1), a k * b k =
      hypersequence a 1 n * b (n + 1) + ∑ k ∈ range (n + 1), hypersequence a 1 k * (b k - b (k + 1))

/-- **Recurrence for power-weighted sums of hypersequences.** Let $a$ be a sequence of complex
numbers, let $a^{(r)}_k$ denote its hypersequence of generation $r$, and for natural numbers
$\ell$, $r$ and $n$ let $t^{(r)}_\ell(n) = \sum_{k=0}^{n} k^\ell a^{(r)}_k$, with the convention
$0^0 = 1$. Then for all natural numbers $\ell$, $r$ and $n$,
$$t^{(r)}_\ell(n) = (n + 1)^\ell a^{(r+1)}_n - \sum_{j=0}^{\ell-1} \binom{\ell}{j} t^{(r+1)}_j(n),$$
where the sum over $j$ is empty when $\ell = 0$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 8, Equation (3.5) (`integers-2024-A70-thm-8`). -/
public theorem_wanted sum_pow_mul_hypersequence_recurrence (a : ℕ → ℂ) (ℓ r n : ℕ) :
    ∑ k ∈ range (n + 1), (k : ℂ) ^ ℓ * hypersequence a r k =
      ((n : ℂ) + 1) ^ ℓ * hypersequence a (r + 1) n -
        ∑ j ∈ range ℓ, (ℓ.choose j : ℂ) *
          ∑ k ∈ range (n + 1), (k : ℂ) ^ j * hypersequence a (r + 1) k

/-- **Power-weighted sums of hypersequences.** Let $a$ be a sequence of complex numbers, let
$a^{(r)}_n$ denote its hypersequence of generation $r$, let
$p_{\ell,m}(x, y) = \sum_{i=0}^{m} (-1)^i \binom{m}{i} (ix + y)^\ell$ be the alternating binomial
power sum, and let $S(j, m)$ denote the Stirling numbers of the second kind. Then for all
natural numbers $\ell$, $n$ and $r$, with the convention $0^0 = 1$,
$$\sum_{k=0}^{n} k^\ell a^{(r)}_k = \sum_{m=0}^{\ell} p_{\ell,m}(1, n + 1)\, a^{(r+m+1)}_n$$
and
$$\sum_{k=0}^{n} k^\ell a^{(r)}_k = \sum_{j=0}^{\ell} \binom{\ell}{j}
\Bigl(\sum_{m=0}^{j} (-1)^m\, m!\, S(j, m)\, a^{(r+m+1)}_n\Bigr) (n + 1)^{\ell-j}.$$

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 9, Equations (3.7) and (3.8)
(`integers-2024-A70-thm-9`). -/
public theorem_wanted sum_pow_mul_hypersequence_eq (a : ℕ → ℂ) (ℓ n r : ℕ) :
    ∑ k ∈ range (n + 1), (k : ℂ) ^ ℓ * hypersequence a r k =
        ∑ m ∈ range (ℓ + 1),
          alternatingBinomialPowerSum ℓ m 1 (n + 1) * hypersequence a (r + m + 1) n ∧
      ∑ k ∈ range (n + 1), (k : ℂ) ^ ℓ * hypersequence a r k =
        ∑ j ∈ range (ℓ + 1), (ℓ.choose j : ℂ) *
          (∑ m ∈ range (j + 1), (-1) ^ m * (m.factorial : ℂ) * (Nat.stirlingSecond j m : ℂ) *
            hypersequence a (r + m + 1) n) * ((n : ℂ) + 1) ^ (ℓ - j)

/-- **Power-weighted sums of a sequence via its hypersequences.** Let $a$ be a sequence of complex
numbers, let $a^{(r)}_n$ denote its hypersequence of generation $r$, let
$p_{\ell,m}(x, y) = \sum_{i=0}^{m} (-1)^i \binom{m}{i} (ix + y)^\ell$ be the alternating binomial
power sum, and let $S(j, m)$ denote the Stirling numbers of the second kind. Then for all
natural numbers $\ell$ and $n$, with the convention $0^0 = 1$,
$$\sum_{k=0}^{n} k^\ell a_k = \sum_{m=0}^{\ell} p_{\ell,m}(1, n + 1)\, a^{(m+1)}_n$$
and
$$\sum_{k=0}^{n} k^\ell a_k = \sum_{j=0}^{\ell} \binom{\ell}{j}
\Bigl(\sum_{m=0}^{j} (-1)^m\, m!\, S(j, m)\, a^{(m+1)}_n\Bigr) (n + 1)^{\ell-j}.$$

This is the case $r = 0$ of the corresponding identity for $\sum_{k=0}^{n} k^\ell a^{(r)}_k$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Corollary 3 (`integers-2024-A70-cor-3`). -/
public theorem_wanted sum_pow_mul_eq (a : ℕ → ℂ) (ℓ n : ℕ) :
    ∑ k ∈ range (n + 1), (k : ℂ) ^ ℓ * a k =
        ∑ m ∈ range (ℓ + 1), alternatingBinomialPowerSum ℓ m 1 (n + 1) * hypersequence a (m + 1) n ∧
      ∑ k ∈ range (n + 1), (k : ℂ) ^ ℓ * a k =
        ∑ j ∈ range (ℓ + 1), (ℓ.choose j : ℂ) *
          (∑ m ∈ range (j + 1), (-1) ^ m * (m.factorial : ℂ) * (Nat.stirlingSecond j m : ℂ) *
            hypersequence a (m + 1) n) * ((n : ℂ) + 1) ^ (ℓ - j)

/-- **Boyadzhiev's and Katsuura's formulas for alternating binomial power sums.** Let
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (kx + y)^\ell$ and let $S(j, m)$ denote the
Stirling numbers of the second kind. For all complex numbers $x, y$ and natural numbers
$\ell, m$:
(i) (Boyadzhiev) $p_{\ell,m}(x, y) = \sum_{j=m}^{\ell} \binom{\ell}{j} (-1)^m m!\, S(j, m)\,
x^j y^{\ell-j}$, where the sum is empty (hence $0$) when $\ell < m$;
(ii) (Katsuura) if $\ell < m$ then $p_{\ell,m}(x, y) = 0$, and $p_{m,m}(x, y) = (-1)^m x^m m!$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Proposition 1 (`integers-2024-A70-prop-1`). -/
public theorem_wanted alternatingBinomialPowerSum_eq_sum_stirlingSecond (x y : ℂ) (ℓ m : ℕ) :
    alternatingBinomialPowerSum ℓ m x y =
        ∑ j ∈ Icc m ℓ, (ℓ.choose j : ℂ) * (-1) ^ m * (m.factorial : ℂ) *
          (Nat.stirlingSecond j m : ℂ) * x ^ j * y ^ (ℓ - j) ∧
      (ℓ < m → alternatingBinomialPowerSum ℓ m x y = 0) ∧
      alternatingBinomialPowerSum m m x y = (-1) ^ m * x ^ m * (m.factorial : ℂ)

/-- **Special values of alternating binomial power sums.** Let
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (kx + y)^\ell$, with $0^0 = 1$, and let
$S(j, m)$ denote the Stirling numbers of the second kind. For all complex numbers $x, y$ and
natural numbers $\ell, m$:
(i) $p_{\ell,m}(x, x) = (-1)^m m!\, S(\ell + 1, m + 1)\, x^\ell$, and in particular
$p_{\ell,m}(1, 1) = (-1)^m m!\, S(\ell + 1, m + 1)$;
(ii) $p_{\ell,m}(0, y) = 0^m y^\ell$;
(iii) $p_{\ell,m}(x, 0) = (-1)^m m!\, S(\ell, m)\, x^\ell$, and in particular
$p_{m+1,m}(1, 0) = (-1)^m m! \binom{m+1}{2}$;
(iv) $p_{\ell,m}(-1, m) = m!\, S(\ell, m)$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Proposition 2 (i)–(iv) (`integers-2024-A70-prop-2`). -/
public theorem_wanted alternatingBinomialPowerSum_special_values (x y : ℂ) (ℓ m : ℕ) :
    alternatingBinomialPowerSum ℓ m x x =
        (-1) ^ m * (m.factorial : ℂ) * (Nat.stirlingSecond (ℓ + 1) (m + 1) : ℂ) * x ^ ℓ ∧
      alternatingBinomialPowerSum ℓ m 1 1 =
        (-1) ^ m * (m.factorial : ℂ) * (Nat.stirlingSecond (ℓ + 1) (m + 1) : ℂ) ∧
      alternatingBinomialPowerSum ℓ m 0 y = 0 ^ m * y ^ ℓ ∧
      alternatingBinomialPowerSum ℓ m x 0 =
        (-1) ^ m * (m.factorial : ℂ) * (Nat.stirlingSecond ℓ m : ℂ) * x ^ ℓ ∧
      alternatingBinomialPowerSum (m + 1) m 1 0 =
        (-1) ^ m * (m.factorial : ℂ) * ((m + 1).choose 2 : ℂ) ∧
      alternatingBinomialPowerSum ℓ m (-1) m = (m.factorial : ℂ) * (Nat.stirlingSecond ℓ m : ℂ)

/-- **Small cases of alternating binomial power sums.** Let
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (kx + y)^\ell$, with $0^0 = 1$. For all
complex numbers $x, y$ and natural numbers $\ell, m$:
(i) $p_{\ell,0}(x, y) = y^\ell$;
(ii) $p_{\ell,1}(x, y) = y^\ell - (x + y)^\ell$;
(iii) $p_{\ell,2}(x, y) = y^\ell - 2(x + y)^\ell + (2x + y)^\ell$;
(iv) if $\ell \ge 1$, then
$p_{\ell,\ell-1}(x, y) = (-1)^{\ell-1} \ell!\, x^{\ell-1} \left(y + \frac{\ell - 1}{2} x\right)$;
(v) $p_{\ell,\ell}(x, y) = (-1)^\ell \ell!\, x^\ell$;
(vi) $p_{0,m}(x, y) = 0^m$;
(vii) $\sum_{m=0}^{\ell} p_{\ell,m}(x, y) = (y - x)^\ell$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Proposition 3 (`integers-2024-A70-prop-3`). -/
public theorem_wanted alternatingBinomialPowerSum_small_cases (x y : ℂ) (ℓ m : ℕ) :
    alternatingBinomialPowerSum ℓ 0 x y = y ^ ℓ ∧
      alternatingBinomialPowerSum ℓ 1 x y = y ^ ℓ - (x + y) ^ ℓ ∧
      alternatingBinomialPowerSum ℓ 2 x y = y ^ ℓ - 2 * (x + y) ^ ℓ + (2 * x + y) ^ ℓ ∧
      (1 ≤ ℓ → alternatingBinomialPowerSum ℓ (ℓ - 1) x y =
        (-1) ^ (ℓ - 1) * (ℓ.factorial : ℂ) * x ^ (ℓ - 1) * (y + ((ℓ : ℂ) - 1) / 2 * x)) ∧
      alternatingBinomialPowerSum ℓ ℓ x y = (-1) ^ ℓ * (ℓ.factorial : ℂ) * x ^ ℓ ∧
      alternatingBinomialPowerSum 0 m x y = 0 ^ m ∧
      ∑ m ∈ range (ℓ + 1), alternatingBinomialPowerSum ℓ m x y = (y - x) ^ ℓ

/-- **Recurrences for alternating binomial power sums.** Let
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (kx + y)^\ell$. For all complex numbers
$x, y$ and natural numbers $\ell, m$ (sums over an empty range are $0$, and $m - 1$ means $0$ when
$m = 0$):
(i) $p_{\ell,m+1}(x, y) = p_{\ell,m}(x, y) - p_{\ell,m}(x, x + y)$;
(ii) $p_{\ell,m}(x, x + y) = \sum_{j=m}^{\ell} \binom{\ell}{j} p_{j,m}(x, y)\, x^{\ell-j}$;
(iii) $p_{\ell,m+1}(x, y) = -\sum_{j=m}^{\ell-1} \binom{\ell}{j} p_{j,m}(x, y)\, x^{\ell-j}$;
(iv) $p_{\ell+1,m}(x, y) = y\, p_{\ell,m}(x, y) - m x\, p_{\ell,m-1}(x, x + y)$;
(v) $p_{\ell+1,m+1}(x, y) = ((m + 1) x + y)\, p_{\ell,m+1}(x, y) -
(m + 1) x\, p_{\ell,m}(x, y)$;
(vi) if $\ell \ge 1$, the complex derivative of $z \mapsto p_{\ell,m}(x, z)$ at $z = y$ is
$\ell\, p_{\ell-1,m}(x, y)$;
(vii) if $\ell \ge 1$, then
$p_{\ell,m}(x, y) = (m x + y)\, p_{\ell-1,m}(x, y) - m x\, p_{\ell-1,m-1}(x, y)$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Proposition 4 (`integers-2024-A70-prop-4`). -/
public theorem_wanted alternatingBinomialPowerSum_recurrences (x y : ℂ) (ℓ m : ℕ) :
    alternatingBinomialPowerSum ℓ (m + 1) x y =
        alternatingBinomialPowerSum ℓ m x y - alternatingBinomialPowerSum ℓ m x (x + y) ∧
      alternatingBinomialPowerSum ℓ m x (x + y) =
        ∑ j ∈ Icc m ℓ, (ℓ.choose j : ℂ) * alternatingBinomialPowerSum j m x y * x ^ (ℓ - j) ∧
      alternatingBinomialPowerSum ℓ (m + 1) x y =
        -∑ j ∈ Ico m ℓ, (ℓ.choose j : ℂ) * alternatingBinomialPowerSum j m x y * x ^ (ℓ - j) ∧
      alternatingBinomialPowerSum (ℓ + 1) m x y =
        y * alternatingBinomialPowerSum ℓ m x y -
          m * x * alternatingBinomialPowerSum ℓ (m - 1) x (x + y) ∧
      alternatingBinomialPowerSum (ℓ + 1) (m + 1) x y =
        ((m + 1) * x + y) * alternatingBinomialPowerSum ℓ (m + 1) x y -
          (m + 1) * x * alternatingBinomialPowerSum ℓ m x y ∧
      (1 ≤ ℓ → deriv (fun z => alternatingBinomialPowerSum ℓ m x z) y =
        ℓ * alternatingBinomialPowerSum (ℓ - 1) m x y) ∧
      (1 ≤ ℓ → alternatingBinomialPowerSum ℓ m x y =
        (m * x + y) * alternatingBinomialPowerSum (ℓ - 1) m x y -
          m * x * alternatingBinomialPowerSum (ℓ - 1) (m - 1) x y)

/-- **Derivative and recurrence of the shifted alternating binomial power sums.** Let
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (kx + y)^\ell$ and, for a complex number
$n$, let $c_{\ell,m}(n) = p_{\ell,m}(1, n + 1)$. For natural numbers $\ell, m \ge 1$ and every
complex number $n$, the complex derivative of $c_{\ell,m}$ at $n$ is $\ell\, c_{\ell-1,m}(n)$, and
$c_{\ell,m}(n) = (m + n + 1)\, c_{\ell-1,m}(n) - m\, c_{\ell-1,m-1}(n)$.

The variable $n$ is complex here because the paper differentiates in $n$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Corollary 4, Equation (3.38) (`integers-2024-A70-cor-4`). -/
public theorem_wanted carlitzSum_deriv_and_recurrence {ℓ m : ℕ} (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m)
    (n : ℂ) :
    deriv (fun z => alternatingBinomialPowerSum ℓ m 1 (z + 1)) n =
        ℓ * alternatingBinomialPowerSum (ℓ - 1) m 1 (n + 1) ∧
      alternatingBinomialPowerSum ℓ m 1 (n + 1) =
        (m + n + 1) * alternatingBinomialPowerSum (ℓ - 1) m 1 (n + 1) -
          m * alternatingBinomialPowerSum (ℓ - 1) (m - 1) 1 (n + 1)

/-- **Sums of $m$th powers via Stirling numbers of the second kind.** For all natural numbers
$n$ and $m$,
$$\sum_{k=1}^{n} k^m = \sum_{k=0}^{m} (-1)^{m-k}\, k!\, \binom{n + k}{k + 1}\, S(m, k),$$
where $S(m, k)$ denotes the Stirling numbers of the second kind.

The paper takes $n \ge 1$; for $n = 0$ both sides vanish, so that case is included.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Corollary 5, Equation (4.4) (`integers-2024-A70-cor-5`). -/
public theorem_wanted sum_pow_eq_sum_stirlingSecond (n m : ℕ) :
    ∑ k ∈ Icc 1 n, (k : ℤ) ^ m =
      ∑ k ∈ range (m + 1),
        (-1) ^ (m - k) * (k.factorial : ℤ) * ((n + k).choose (k + 1) : ℤ) *
          (Nat.stirlingSecond m k : ℤ)

/-- **Alternating binomial expansion of a shifted binomial coefficient.** For all natural numbers
$m$, $n$ and $k$,
$$\binom{n+m-k-1}{m} = \sum_{j=0}^{k} (-1)^j \binom{k}{j} \binom{n+m-j-1}{m-j},$$
where, for an integer $x$ and a natural number $i$, $\binom{x}{i} = x(x-1)\cdots(x-i+1)/i!$ is
the generalized binomial coefficient, and the term $\binom{n+m-j-1}{m-j}$ is taken to be $0$
when $j > m$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Lemma 1, Equation (4.10) (`integers-2024-A70-lem-1`). -/
public theorem_wanted ringChoose_sub_eq_sum (m n k : ℕ) :
    Ring.choose ((n : ℤ) + m - k - 1) m =
      ∑ j ∈ range (k + 1), (-1) ^ j * (k.choose j : ℤ) *
        (if j ≤ m then Ring.choose ((n : ℤ) + m - j - 1) (m - j) else 0)

/-- **Powers of $k + 1$ via Stirling numbers of the second kind.** For all natural numbers $k$
and $\ell$,
$$(k + 1)^\ell = \sum_{j=0}^{k} \binom{k}{j}\, j!\, S(\ell + 1, j + 1),$$
where $S(i, j)$ denotes the Stirling numbers of the second kind.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Lemma 2, Equation (4.11) (`integers-2024-A70-lem-2`). -/
public theorem_wanted succ_pow_eq_sum_stirlingSecond (k ℓ : ℕ) :
    (k + 1) ^ ℓ = ∑ j ∈ range (k + 1), k.choose j * j.factorial * Nat.stirlingSecond (ℓ + 1) (j + 1)

/-- **Power-weighted sums of Fibonacci numbers.** Let $F_k$ denote the Fibonacci numbers and let
$p_{\ell,m}(x, y) = \sum_{i=0}^{m} (-1)^i \binom{m}{i} (ix + y)^\ell$ be the alternating binomial
power sum. Then for all natural numbers $\ell$ and $n$, with the convention $0^0 = 1$,
$$\sum_{k=0}^{n} k^\ell F_k = \sum_{m=0}^{\ell} p_{\ell,m}(1, n + 1)\, F_{n+2(m+1)} -
\sum_{m=0}^{\ell} p_{\ell,m}(1, 1)\, F_{2(m+1)}.$$

The paper's conjecture on the constant term, stated after this theorem, is not included.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 10, Equation (4.7) (`integers-2024-A70-thm-10`). -/
public theorem_wanted sum_pow_mul_fib_eq (ℓ n : ℕ) :
    ∑ k ∈ range (n + 1), (k : ℂ) ^ ℓ * Nat.fib k =
      ∑ m ∈ range (ℓ + 1), alternatingBinomialPowerSum ℓ m 1 (n + 1) * Nat.fib (n + 2 * (m + 1)) -
        ∑ m ∈ range (ℓ + 1), alternatingBinomialPowerSum ℓ m 1 1 * Nat.fib (2 * (m + 1))

/-- **Power-weighted sums of Lucas numbers.** Let $L_k$ denote the Lucas numbers, so $L_0 = 2$,
$L_1 = 1$ and $L_{k+2} = L_{k+1} + L_k$, and let
$p_{\ell,m}(x, y) = \sum_{i=0}^{m} (-1)^i \binom{m}{i} (ix + y)^\ell$ be the alternating binomial
power sum. Then for all natural numbers $\ell$ and $n$, with the convention $0^0 = 1$,
$$\sum_{k=0}^{n} k^\ell L_k = \sum_{m=0}^{\ell} p_{\ell,m}(1, n + 1)\, L_{n+2(m+1)} -
\sum_{m=0}^{\ell} p_{\ell,m}(1, 1)\, L_{2(m+1)} + L_0 \cdot 0^\ell.$$

The paper's conjecture on the constant term, stated after this theorem, is not included.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 11, Equation (4.9) (`integers-2024-A70-thm-11`). -/
public theorem_wanted sum_pow_mul_lucas_eq (ℓ n : ℕ) :
    ∑ k ∈ range (n + 1), (k : ℂ) ^ ℓ * lucasNumber k =
      ∑ m ∈ range (ℓ + 1),
          alternatingBinomialPowerSum ℓ m 1 (n + 1) * lucasNumber (n + 2 * (m + 1)) -
        ∑ m ∈ range (ℓ + 1), alternatingBinomialPowerSum ℓ m 1 1 * lucasNumber (2 * (m + 1)) +
        lucasNumber 0 * 0 ^ ℓ

end

end MetaMathlibExt
