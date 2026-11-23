/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Basic.Complex.Basic
public import MathlibExt.FieldTheory.Finite.PermutationPolynomial

/-!
# Permutation polynomials of the form `∑ n^t X^(n+a)` and related lemmas

Statements from Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on
Ordered Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12: the
monomial and power-sum criteria the paper quotes, its binomial-sum identity, and its two
new classes of permutation polynomials over `𝔽_p`. Permutation polynomials use MathlibExt's
`Polynomial.IsPermutationPolynomial` (bijective evaluation map).
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- **Monomial permutation polynomials of a finite field.** Let $K$ be a finite field with $q$
elements and let $d \ge 1$ be an integer. Then $X^d$ is a permutation polynomial of $K$ if and
only if $\gcd(d, q - 1) = 1$.

The hypothesis $d \ge 1$ is needed: for $d = 0$ and $q = 2$ the condition $\gcd(d, q - 1) = 1$
holds, but $X^0 = 1$ is constant.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Lemma 2
(`integers-2024-A12-lem-2`). -/
public theorem_wanted isPermutationPolynomial_X_pow_iff_coprime {K : Type*} [Field K]
    [Fintype K] {d : ℕ} (hd : 0 < d) :
    (X ^ d : K[X]).IsPermutationPolynomial ↔ d.Coprime (Fintype.card K - 1)

/-- **Power-sum criterion for distinct elements of a finite field.** Let $K$ be a finite field
with $q$ elements and let $a_1, \dots, a_q \in K$. Then $a_1, \dots, a_q$ are pairwise distinct
if and only if $\sum_{i=1}^{q} a_i^t = 0$ for every $t = 0, 1, \dots, q - 2$ and
$\sum_{i=1}^{q} a_i^{q-1} = -1$, where $0^0 = 1$.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Lemma 3
(`integers-2024-A12-lem-3`). -/
public theorem_wanted injective_iff_sum_pow_eq {K : Type*} [Field K] [Fintype K]
    (a : Fin (Fintype.card K) → K) :
    Function.Injective a ↔
      (∀ t : ℕ, t < Fintype.card K - 1 → ∑ i, a i ^ t = 0) ∧
        ∑ i, a i ^ (Fintype.card K - 1) = -1

/-- **Alternating binomial sums of powers.** Let $x, y, k \in \mathbb{C}$ and let $n, m$ be
positive integers. If $n = m$, then

$$\sum_{i=0}^{n} (-1)^i \binom{n}{i} (kx + iy)^m = (-1)^n y^n n!,$$

and if $m < n$, then $\sum_{i=0}^{n} (-1)^i \binom{n}{i} (kx + iy)^m = 0$.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Theorem 3
(`integers-2024-A12-thm-3`). -/
public theorem_wanted sum_neg_one_pow_choose_mul_pow (x y k : ℂ) {n m : ℕ} (hn : 0 < n)
    (hm : 0 < m) :
    (n = m → ∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * (n.choose i : ℂ) * (k * x + i * y) ^ m =
          (-1) ^ n * y ^ n * (n.factorial : ℂ)) ∧
      (m < n → ∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * (n.choose i : ℂ) * (k * x + i * y) ^ m = 0)

/-- **Shifted power-sum permutation polynomials of a prime field.** Let $p$ be an odd prime and
let $k, t, a$ be positive integers with $\gcd(a + 1, p - 1) = 1$ and $k \equiv 1 \pmod{p(p-1)}$.
Suppose that $p - 1 \nmid t$ or $p^2 \mid k - 1$. Then the polynomial
$\sum_{n=1}^{k} n^t X^{n+a}$, with coefficients reduced modulo $p$, is a permutation polynomial
of $\mathbb{F}_p$.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Corollary 1
(`integers-2024-A12-cor-1`). -/
public theorem_wanted isPermutationPolynomial_sum_pow_mul_X_pow_add {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {k t a : ℕ} (hk : 0 < k) (ht : 0 < t) (ha : 0 < a)
    (hka : (a + 1).Coprime (p - 1)) (hkcong : k ≡ 1 [MOD p * (p - 1)])
    (hcases : ¬(p - 1) ∣ t ∨ p ^ 2 ∣ k - 1) :
    (∑ n ∈ Finset.Icc 1 k, C ((n : ZMod p) ^ t) * X ^ (n + a)).IsPermutationPolynomial

/-- **Dilated power-sum permutation polynomials of a prime field.** Let $p$ be an odd prime and
let $k, t, a$ be positive integers with $p \nmid a$, $\gcd(a, p - 1) = 1$ and
$k \equiv 1 \pmod{p(p-1)}$. Suppose that $p - 1 \nmid t$ or $p^2 \mid k - 1$. Then the
polynomial $\sum_{n=1}^{k} (an)^t X^{an}$, with coefficients reduced modulo $p$, is a
permutation polynomial of $\mathbb{F}_p$.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Corollary 3
(`integers-2024-A12-cor-3`). -/
public theorem_wanted isPermutationPolynomial_sum_mul_pow_mul_X_pow_mul {p : ℕ}
    [Fact p.Prime] (hp : p ≠ 2) {k t a : ℕ} (hk : 0 < k) (ht : 0 < t) (ha : 0 < a)
    (hpa : ¬p ∣ a) (hap : a.Coprime (p - 1)) (hkcong : k ≡ 1 [MOD p * (p - 1)])
    (hcases : ¬(p - 1) ∣ t ∨ p ^ 2 ∣ k - 1) :
    (∑ n ∈ Finset.Icc 1 k,
      C (((a * n : ℕ) : ZMod p) ^ t) * X ^ (a * n)).IsPermutationPolynomial

/-- **Rational form of the power-weighted geometric sum.** For positive integers $t$ and $k$,
the following identity holds in $\mathbb{Z}[X]$:

$$(1 - X)^{t+1} \sum_{n=1}^{k} n^t X^n =
\sum_{n=1}^{t} \Bigl(\sum_{i=0}^{n-1} (-1)^i \binom{t+1}{i} (n - i)^t\Bigr) X^n +
\sum_{m=1}^{t+1} \Bigl(\sum_{i=m}^{t+1} (-1)^i \binom{t+1}{i} (k + m - i)^t\Bigr) X^{k+m}.$$

Equivalently, for every $x \ne 1$ the value $h_t^k(x) = \sum_{n=1}^{k} n^t x^n$ is the
right-hand side at $x$ divided by $(1 - x)^{t+1}$, which is the form the source states.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Lemma 4
(`integers-2024-A12-lem-4`). -/
public theorem_wanted one_sub_X_pow_mul_sum_pow_mul_X_pow (t k : ℕ) (ht : 0 < t) (hk : 0 < k) :
    (1 - X : ℤ[X]) ^ (t + 1) * ∑ n ∈ Finset.Icc 1 k, C ((n : ℤ) ^ t) * X ^ n =
      ∑ n ∈ Finset.Icc 1 t, C (∑ i ∈ Finset.range n,
          (-1) ^ i * ((t + 1).choose i : ℤ) * ((n : ℤ) - i) ^ t) * X ^ n +
        ∑ m ∈ Finset.Icc 1 (t + 1), C (∑ i ∈ Finset.Icc m (t + 1),
          (-1) ^ i * ((t + 1).choose i : ℤ) * ((k : ℤ) + m - i) ^ t) * X ^ (k + m)

/-- **Vishwakarma–Singh congruence for ordered partitions.** Let $p$ be an odd prime and let
$k, s, t$ be positive integers with $s \le p - 2$ and $k \equiv 1 \pmod{p(p-1)}$, such that
$p^2 \mid k - 1$ whenever $p - 1 \mid t$. Let $\mu = \lfloor ks/(p - 1) \rfloor$. Then

$$\sum_{j=1}^{\mu} \sum_{\omega} (\omega_1 \cdots \omega_s)^t \equiv 0 \pmod{p},$$

where for each $j$ the inner sum runs over all $s$-tuples $\omega = (\omega_1, \dots, \omega_s)$
with entries in $\{1, \dots, k\}$ and $\omega_1 + \cdots + \omega_s = j(p - 1)$.

The source states the hypothesis $s \not\equiv 0 \pmod{p}$ in place of $s \le p - 2$, the range
of Hermite's criterion used in its proof; with that hypothesis the claim fails, e.g. for $p = 3$,
$k = 1$, $s = 2$, $t = 1$ the sum is $1$.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Theorem 1
(`integers-2024-A12-thm-1`). -/
public theorem_wanted prime_dvd_sum_compositions_prod_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {k s t : ℕ} (hk : 0 < k) (hs : 0 < s) (hsp : s ≤ p - 2) (ht : 0 < t)
    (hkcong : k ≡ 1 [MOD p * (p - 1)]) (hcases : (p - 1) ∣ t → p ^ 2 ∣ k - 1) :
    p ∣ ∑ j ∈ Finset.Icc 1 (k * s / (p - 1)),
      ∑ ω ∈ (Fintype.piFinset fun _ : Fin s => Finset.Icc 1 k).filter
          (fun ω => ∑ i, ω i = j * (p - 1)),
        (∏ i, ω i) ^ t

/-- **Vishwakarma–Singh congruence for ordered partitions, linear case.** Let $p$ be an odd
prime and let $k, s$ be positive integers with $s \le p - 2$ and $k \equiv 1 \pmod{p(p-1)}$.
Let $\mu = \lfloor ks/(p - 1) \rfloor$. Then

$$\sum_{j=1}^{\mu} \sum_{\omega} \omega_1 \cdots \omega_s \equiv 0 \pmod{p},$$

where for each $j$ the inner sum runs over all $s$-tuples $\omega = (\omega_1, \dots, \omega_s)$
with entries in $\{1, \dots, k\}$ and $\omega_1 + \cdots + \omega_s = j(p - 1)$.

This is the case $t = 1$ of the source's Theorem 1. The source states the hypothesis
$s \not\equiv 0 \pmod{p}$ in place of $s \le p - 2$; with that hypothesis the claim fails, e.g.
for $p = 3$, $k = 7$, $s = 2$ the sum is $400 \equiv 1 \pmod{3}$.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Corollary 2
(`integers-2024-A12-cor-2`). -/
public theorem_wanted prime_dvd_sum_compositions_prod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {k s : ℕ} (hk : 0 < k) (hs : 0 < s) (hsp : s ≤ p - 2) (hkcong : k ≡ 1 [MOD p * (p - 1)]) :
    p ∣ ∑ j ∈ Finset.Icc 1 (k * s / (p - 1)),
      ∑ ω ∈ (Fintype.piFinset fun _ : Fin s => Finset.Icc 1 k).filter
          (fun ω => ∑ i, ω i = j * (p - 1)),
        ∏ i, ω i

/-- **Vishwakarma–Singh congruence for ordered partitions into multiples.** Let $p$ be an odd
prime and let $a, k, s, t$ be positive integers with $\gcd(a, p - 1) = 1$, $s \le p - 2$ and
$k \equiv 1 \pmod{p(p-1)}$, such that $p^2 \mid k - 1$ whenever $p - 1 \mid t$. Let
$\mu = \lfloor aks/(p - 1) \rfloor$. Then

$$\sum_{j=1}^{\mu} \sum_{\omega} (\omega_1 \cdots \omega_s)^t \equiv 0 \pmod{p},$$

where for each $j$ the inner sum runs over all $s$-tuples $\omega = (\omega_1, \dots, \omega_s)$
with entries in $\{an : 1 \le n \le k\}$ and $\omega_1 + \cdots + \omega_s = j(p - 1)$.

The source states this with two differences. It assumes $s \not\equiv 0 \pmod{p}$ in place of
$s \le p - 2$; with that hypothesis the claim fails, e.g. for $a = 1$, $p = 3$, $k = 7$, $s = 2$,
$t = 1$. It takes $\mu = \lfloor ks/(p - 1) \rfloor$; with that bound the claim fails for $a > 1$,
e.g. for $p = 5$, $a = 3$, $k = 21$, $s = t = 1$ the sum is $12$. The bound
$\lfloor aks/(p - 1) \rfloor$ covers every multiple of $p - 1$ up to $aks$, the degree of the
$s$-th power of $\sum_{n=1}^{k} (an)^t X^{an}$, to which the proof applies Hermite's criterion.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Corollary 4
(`integers-2024-A12-cor-4`). -/
public theorem_wanted prime_dvd_sum_compositions_mul_prod_pow {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {a k s t : ℕ} (ha : 0 < a) (hap : a.Coprime (p - 1)) (hk : 0 < k) (hs : 0 < s)
    (hsp : s ≤ p - 2) (ht : 0 < t) (hkcong : k ≡ 1 [MOD p * (p - 1)])
    (hcases : (p - 1) ∣ t → p ^ 2 ∣ k - 1) :
    p ∣ ∑ j ∈ Finset.Icc 1 (a * k * s / (p - 1)),
      ∑ ω ∈ (Fintype.piFinset fun _ : Fin s => (Finset.Icc 1 k).image (a * ·)).filter
          (fun ω => ∑ i, ω i = j * (p - 1)),
        (∏ i, ω i) ^ t

end

end MetaMathlibExt
