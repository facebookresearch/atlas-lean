/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.RingTheory.Coprime.Basic
import MathlibExt.NumberTheory.PrimeDvdPowAddOfDvdRadicalCoeffsGcd
import MathlibExt.NumberTheory.RadicalCoefficientCommonPrime
import Mathlib.Data.Nat.Prime.Basic

/-!
# Coprime radical-expansion coefficients

The coefficients of every positive power of `u + v^{1/N}` have gcd one when `u` and `v`
are coprime, `X ^ N - v` is irreducible over `ℚ`, `N ≥ 2`, and the signed norm
`u ^ N + (-1) ^ (N + 1) * v` is coprime to `N`.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Corollary 9
(`jis-2025-25.2.2-cor-9`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Coprime coefficients when $u^N + (-1)^{N+1} v$ is coprime to $N$.** Let $N \ge 2$, let
$u, v$ be coprime natural numbers such that $x^N - v$ is irreducible over $\mathbb{Q}$, let
$\theta = v^{1/N}$ be the nonnegative real $N$-th root of $v$, and let $a_{n,i}$ (for natural $n$
and $0 \le i \le N - 1$) be integers with $(u + \theta)^n = \sum_{i=0}^{N-1} a_{n,i} \theta^i$
for every $n \ge 1$. If $u^N + (-1)^{N+1} v$ and $N$ are coprime integers, then for every
$n \ge 1$ the greatest common divisor of $a_{n,0}, \dots, a_{n,N-1}$ is $1$.

The paper assumes $N \ge 4$; the cases $N = 2, 3$ also hold, while $N = 1$ fails.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Corollary 9
(`jis-2025-25.2.2-cor-9`). -/
public theorem gcd_radical_expansion_coeffs_eq_one_of_coprime {N u v : ℕ} (hN : 2 ≤ N)
    (huv : u.Coprime v)
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (a : ℕ → Fin N → ℤ)
    (ha : ∀ n, 1 ≤ n → ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a n i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ))
    (hM : IsCoprime ((u : ℤ) ^ N + (-1) ^ (N + 1) * v) (N : ℤ)) (n : ℕ) (hn : 1 ≤ n) :
    Finset.univ.gcd (a n) = 1 := by
  rw [← Finset.normalize_gcd, normalize_eq_one]
  apply Int.isUnit_iff_natAbs_eq.mpr
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hpd
  have hpd' : (p : ℤ) ∣ Finset.univ.gcd (a n) := Int.natCast_dvd.mpr hpd
  have hpM := prime_dvd_pow_add_of_dvd_radical_coeffs_gcd hirr a ha n hn p hp hpd'
  have hpN := prime_dvd_gcd_pow_add_radical_coeffs hN huv hirr a ha n hn p hp
    (dvd_gcd hpM hpd')
  have hunit := hM.isUnit_of_dvd' hpM (Int.natCast_dvd_natCast.mpr hpN)
  exact hp.ne_one (by simpa using Int.natAbs_of_isUnit hunit)

end

end MetaMathlibExt
