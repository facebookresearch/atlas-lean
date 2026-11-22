/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Bernoulli.PolyBernoulliDuality
public import WantedExt.NumberTheory.EulerPolynomialFormulasWanted
public import WantedExt.NumberTheory.GobelSequenceWanted
public import Mathlib.NumberTheory.Harmonic.Defs

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

/--
**Poly-Bernoulli polynomials.** For a natural number $n$, an integer $k$ and a rational number
$x$, the poly-Bernoulli polynomial of degree $n$ and order $k$ at $x$ is the rational number
$$B_n^{(k)}(x) = \sum_{i=0}^{n} \binom{n}{i} B_i^{(k)} x^{n-i},$$
where $B_i^{(k)}$ are the poly-Bernoulli numbers.

These are the coefficients of the generating function
$\frac{\mathrm{Li}_k(1-e^{-t})}{1-e^{-t}} e^{xt} = \sum_{n \ge 0} B_n^{(k)}(x) \frac{t^n}{n!}$,
which is how the source defines them.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, definition of
poly-Bernoulli polynomials before Corollary 3.
-/
public def polyBernoulliPoly (n : ℕ) (p : ℤ) (x : ℚ) : ℚ :=
  ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℚ) * polyBernoulli i p * x ^ (n - i)

/--
**Poly-Bernoulli polynomials at zero.** For every natural number $n$ and every integer $k$, the
poly-Bernoulli polynomial of degree $n$ and order $k$ evaluated at $0$ equals the
poly-Bernoulli number of index $n$ and order $k$: $B_n^{(k)}(0) = B_n^{(k)}$.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, definition of
poly-Bernoulli polynomials before Corollary 3.
-/
public theorem polyBernoulliPoly_zero (n : ℕ) (p : ℤ) :
    polyBernoulliPoly n p 0 = polyBernoulli n p := by
  rw [polyBernoulliPoly, Finset.sum_range_succ]
  have hzero :
      (∑ i ∈ Finset.range n,
        (n.choose i : ℚ) * polyBernoulli i p * (0 : ℚ) ^ (n - i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hsub : n - i ≠ 0 := by omega
    simp [hsub]
  rw [hzero]
  simp

/--
**Poly-Bernoulli polynomials of degree zero.** For every integer $k$ and every rational number
$x$, the poly-Bernoulli polynomial of degree $0$ and order $k$ satisfies $B_0^{(k)}(x) = 1$.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, definition of
poly-Bernoulli polynomials before Corollary 3.
-/
public theorem polyBernoulliPoly_zero_index (p : ℤ) (x : ℚ) :
    polyBernoulliPoly 0 p x = 1 := by
  simp [polyBernoulliPoly, polyBernoulli]

/--
**Bernoulli numbers from Stirling and harmonic numbers.** Let $j < n$ be natural numbers. Write
${n \brace k}$ for the Stirling numbers of the second kind, ${k \brack j}$ for the unsigned
Stirling numbers of the first kind (the number of permutations of $k$ elements with exactly $j$
cycles), $H_k = \sum_{i=1}^{k} 1/i$ for the harmonic numbers (so $H_0 = 0$), and $B_m$ for the
Bernoulli numbers, normalized so that $B_1 = -1/2$. Then, in the rational numbers,

$$
\sum_{k=j}^{n} (-1)^{k-j} {n \brace k} {k \brack j} H_k
= \left(\binom{n}{j} - 1\right) \frac{B_{n-j}}{n-j}.
$$

The paper also covers the diagonal case $n = j$, reading the right-hand side as a limit (both
sides are then $H_j$); that case is not included here.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Theorem 1,
equation (5).
-/
public theorem_wanted sum_stirling_harmonic_eq_bernoulli (n j : ℕ) (hjn : j < n) :
    (∑ k ∈ Finset.Icc j n,
      (-1 : ℚ) ^ (k - j) * (Nat.stirlingSecond n k : ℚ) *
        (Nat.stirlingFirst k j : ℚ) * harmonic k) =
      ((n.choose j : ℚ) - 1) * bernoulli (n - j) / (n - j : ℚ)

/--
**A Bernoulli–harmonic power-sum identity.** Let $B_j$ denote the Bernoulli numbers with
$B_1 = -\tfrac12$, and let $H_m = \sum_{i=1}^{m} 1/i$ denote the harmonic numbers. For all
positive integers $n$ and $m$,
$$\sum_{j=1}^{n} \left(\binom{n}{j} - 1\right) \frac{B_j}{j} m^{n-j} =
m^n (H_m - H_n) - \sum_{j=1}^{m} \frac{(m-j)^n}{j}.$$

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 1,
equation (11).
-/
public theorem_wanted sum_bernoulli_harmonic_power_identity (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) :
    (∑ j ∈ Finset.Icc 1 n,
      ((n.choose j : ℚ) - 1) * (bernoulli j / (j : ℚ)) * (m : ℚ) ^ (n - j)) =
      (m : ℚ) ^ n * (harmonic m - harmonic n) -
        ∑ j ∈ Finset.Icc 1 m, ((m - j : ℕ) : ℚ) ^ n / (j : ℚ)

/--
**A weighted Bernoulli sum with factors $1 - 2^j$.** Let $B_j$ denote the Bernoulli numbers
with $B_1 = -\tfrac12$. For every positive integer $n$,
$$\sum_{j=1}^{n} \left(\binom{n}{j} + 1\right) \frac{B_j}{j} \left(1 - 2^j\right) = 1.$$

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 2,
equation (14).
-/
public theorem_wanted sum_bernoulli_one_sub_two_pow (n : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.Icc 1 n,
      ((n.choose j : ℚ) + 1) * (bernoulli j / (j : ℚ)) *
        (1 - (2 : ℚ) ^ j)) = 1

/--
**Sums of Bernoulli numbers via poly-Bernoulli polynomials.** Let $B_j$ denote the Bernoulli
numbers with $B_1 = -\tfrac12$, let $B_n^{(2)}$ denote the poly-Bernoulli numbers of order $2$,
and let $B_n^{(2)}(x)$ denote the poly-Bernoulli polynomials of order $2$. For every natural
number $n \ge 2$,
$$\sum_{j=0}^{n} B_j = B_n^{(2)}(1) + B_n - B_n^{(2)} - 1.$$

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 3.
-/
public theorem_wanted sum_bernoulli_eq_polyBernoulli (n : ℕ) (hn : 2 ≤ n) :
    (∑ j ∈ Finset.range (n + 1), bernoulli j) =
      polyBernoulliPoly n 2 1 + bernoulli n - polyBernoulli n 2 - 1

/--
**The congruence $\sum_{j=0}^{p} pB_j \equiv -1 \pmod p$.** Let $B_j$ denote the Bernoulli
numbers with $B_1 = -\tfrac12$. For every odd prime $p$, the rational number
$S = \sum_{j=0}^{p} p B_j$ has denominator not divisible by $p$, and its residue modulo $p$ (its
numerator times the inverse of its denominator in $\mathbb{Z}/p\mathbb{Z}$) equals $-1$.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 4,
equation (23).
-/
public theorem_wanted sum_prime_mul_bernoulli_mod_prime (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬p ∣ (∑ j ∈ Finset.range (p + 1), (p : ℚ) * bernoulli j).den ∧
      ratResidue p (∑ j ∈ Finset.range (p + 1), (p : ℚ) * bernoulli j) =
        ratResidue p (-1)

/--
**The congruence $\sum_{j=0}^{p-3} B_j \equiv -1 \pmod p$.** Let $B_j$ denote the Bernoulli
numbers with $B_1 = -\tfrac12$. For every prime $p \ge 5$, the rational number
$S = B_0 + B_1 + \dots + B_{p-3}$ has denominator not divisible by $p$, and its residue modulo
$p$ (its numerator times the inverse of its denominator in $\mathbb{Z}/p\mathbb{Z}$) equals $-1$.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 4,
equation (24).
-/
public theorem_wanted sum_bernoulli_to_prime_sub_three_mod_prime (p : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬p ∣ (∑ j ∈ Finset.range (p - 2), bernoulli j).den ∧
      ratResidue p (∑ j ∈ Finset.range (p - 2), bernoulli j) =
        ratResidue p (-1)

/--
**The congruence $\sum_{j=0}^{p} E_j(0) \equiv 3/2 \pmod p$.** Let $E_j(x)$ denote the Euler
polynomials. For every odd prime $p$, the rational number $S = E_0(0) + E_1(0) + \dots + E_p(0)$
has denominator not divisible by $p$, and its residue modulo $p$ (its numerator times the
inverse of its denominator in $\mathbb{Z}/p\mathbb{Z}$) equals $3 \cdot 2^{-1}$.

The values $E_j(0)$ are the Euler numbers of the source; they come from the generating function
$2e^{xt}/(e^t + 1)$ and begin $1, -\tfrac12, 0, \tfrac14$.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 4,
equation (25).
-/
public theorem_wanted sum_euler_eval_zero_mod_prime (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬p ∣ (∑ j ∈ Finset.range (p + 1), (eulerPoly j).eval 0).den ∧
      ratResidue p (∑ j ∈ Finset.range (p + 1), (eulerPoly j).eval 0) =
        ratResidue p (3 / 2)

/--
**The congruence $p\sum_{j=0}^{p} B_j/(p-j+1) \equiv -1 \pmod p$.** Let $B_j$ denote the
Bernoulli numbers with $B_1 = -\tfrac12$. For every odd prime $p$, the rational number
$$S = p \sum_{j=0}^{p} \frac{B_j}{p-j+1}$$
has denominator not divisible by $p$, and its residue modulo $p$ (its numerator times the
inverse of its denominator in $\mathbb{Z}/p\mathbb{Z}$) equals $-1$.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 4,
equation (26).
-/
public theorem_wanted prime_mul_sum_bernoulli_div_mod_prime (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬p ∣ ((p : ℚ) * ∑ j ∈ Finset.range (p + 1),
      bernoulli j / ((p - j + 1 : ℕ) : ℚ)).den ∧
      ratResidue p ((p : ℚ) * ∑ j ∈ Finset.range (p + 1),
        bernoulli j / ((p - j + 1 : ℕ) : ℚ)) = ratResidue p (-1)

end

end MetaMathlibExt
