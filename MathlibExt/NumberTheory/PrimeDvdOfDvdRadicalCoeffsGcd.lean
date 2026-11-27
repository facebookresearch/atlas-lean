/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import MathlibExt.NumberTheory.PrimeDvdPowAddOfDvdRadicalCoeffsGcd
import MathlibExt.NumberTheory.RadicalCoefficientCommonPrime

/-!
# Prime divisors of the radical coefficient gcd divide the root degree

Combine divisibility of the norm by a prime dividing the coefficient gcd with the theorem that
common prime divisors of the norm and the coefficient gcd divide the root degree.
-/

namespace MetaMathlibExt

/-- **Primes dividing the coefficient gcd of $(u + v^{1/N})^n$ divide $N$.** Let $N \ge 2$ and
let $u, v$ be coprime natural numbers such that $x^N - v$ is irreducible over $\mathbb{Q}$. Write
$\theta = v^{1/N}$ for the nonnegative real $N$-th root of $v$, and let $a_{n,i}$ be integers
($n \ge 1$, $0 \le i < N$) with $(u + \theta)^n = \sum_{i=0}^{N-1} a_{n,i} \theta^i$ for every
$n \ge 1$. If $n \ge 1$ and $p$ is a prime dividing $D_n = \gcd(a_{n,0}, \dots, a_{n,N-1})$,
then $p$ divides $N$.

The paper's section assumes $N \ge 4$; the cases $N = 2, 3$ also hold, while $N = 1$ fails
(there $D_n = (u + v)^n$).

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Lemma 8
(`jis-2025-25.2.2-lem-8`). -/
public theorem prime_dvd_of_dvd_radical_coeffs_gcd {N u v : ℕ} (hN : 2 ≤ N)
    (huv : u.Coprime v)
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (a : ℕ → Fin N → ℤ)
    (ha : ∀ n, 1 ≤ n → ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a n i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ))
    (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hpd : (p : ℤ) ∣ Finset.univ.gcd (a n)) :
    p ∣ N := by
  have hnorm := prime_dvd_pow_add_of_dvd_radical_coeffs_gcd hirr a ha n hn p hp hpd
  exact prime_dvd_gcd_pow_add_radical_coeffs hN huv hirr a ha n hn p hp (dvd_gcd hnorm hpd)

end MetaMathlibExt
