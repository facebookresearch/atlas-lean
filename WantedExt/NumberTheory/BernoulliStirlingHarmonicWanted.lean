/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Bernoulli.PolyBernoulliDuality
public import MathlibExt.NumberTheory.Bernoulli.StirlingHarmonic
public import MathlibExt.NumberTheory.Bernoulli.SumModPrime
public import MathlibExt.NumberTheory.Bernoulli.TruncatedSumModPrime
public import MathlibExt.NumberTheory.Bernoulli.WeightedSum
public import WantedExt.NumberTheory.EulerPolynomialFormulasWanted
public import WantedExt.NumberTheory.GobelSequenceWanted
public import Mathlib.NumberTheory.Harmonic.Defs

/-
Statements of the same source proved in modules this file imports:
`MathlibExt.NumberTheory.Bernoulli.WeightedSum` (Corollary 2, equation (14)),
`MathlibExt.NumberTheory.Bernoulli.SumModPrime` (Corollary 4, equation (23),
`sum_prime_mul_bernoulli_mod_prime`), and
`MathlibExt.NumberTheory.Bernoulli.TruncatedSumModPrime` (Corollary 4, equation (24)).
-/

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
