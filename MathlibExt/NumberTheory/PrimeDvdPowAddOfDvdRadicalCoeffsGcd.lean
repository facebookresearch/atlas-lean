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
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.KummerPolynomial

/-!
# Prime divisors of radical-expansion coefficients

A prime dividing the coefficient gcd of `(u + θ) ^ n`, where `θ ^ N = v` and `X ^ N - v` is
irreducible, divides the norm of `u + θ`. Modulo that prime, `X ^ N - v` divides `(X + u) ^ n`,
so its positive degree forces it to have `-u` as a root.
-/

namespace MetaMathlibExt

open Polynomial

/-- **Primes dividing the coefficient gcd of $(u + v^{1/N})^n$ divide the norm.** Let $u, v, N$
be natural numbers such that $x^N - v$ is irreducible over $\mathbb{Q}$. Write $\theta = v^{1/N}$
for the nonnegative real $N$-th root of $v$, and let $a_{n,i}$ be integers ($n \ge 1$,
$0 \le i < N$) with $(u + \theta)^n = \sum_{i=0}^{N-1} a_{n,i} \theta^i$ for every $n \ge 1$. If
$n \ge 1$ and $p$ is a prime dividing $D_n = \gcd(a_{n,0}, \dots, a_{n,N-1})$, then $p$ divides
$u^N + (-1)^{N+1} v$, the norm of $u + \theta$.

The paper's section assumes $N \ge 4$ and $u, v$ coprime; neither is needed here.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Lemma 7
(`jis-2025-25.2.2-lem-7`). -/
public theorem prime_dvd_pow_add_of_dvd_radical_coeffs_gcd {N u v : ℕ}
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (a : ℕ → Fin N → ℤ)
    (ha : ∀ n, 1 ≤ n → ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a n i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ))
    (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hpd : (p : ℤ) ∣ Finset.univ.gcd (a n)) :
    (p : ℤ) ∣ (u : ℤ) ^ N + (-1) ^ (N + 1) * v := by
  have hN := ne_zero_of_irreducible_X_pow_sub_C hirr
  let θ := (v : ℝ) ^ (1 / (N : ℝ))
  have hθ : θ ^ N = v := by
    simpa only [θ, one_div] using Real.rpow_inv_natCast_pow (Nat.cast_nonneg v) hN
  have hmin : X ^ N - C (v : ℚ) = minpoly ℚ θ :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hθ]) (monic_X_pow_sub_C _ hN)
  -- The expansion identity at θ gives divisibility over ℚ, which descends to ℤ by monicity.
  let F : ℤ[X] := (X + C (u : ℤ)) ^ n - ∑ i : Fin N, C (a n i) * X ^ (i : ℕ)
  have hdvd : X ^ N - C (v : ℤ) ∣ F := by
    apply (map_dvd_map (Int.castRingHom ℚ) Int.cast_injective (monic_X_pow_sub_C _ hN)).mp
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, map_natCast, hmin]
    apply minpoly.dvd ℚ θ
    simpa [F, Polynomial.map_sum, θ, add_comm (u : ℝ), sub_eq_zero] using ha n hn
  -- Every coordinate vanishes modulo p, leaving a divisor of a power of a linear polynomial.
  let : Fact p.Prime := ⟨hp⟩
  have hcoeff (i : Fin N) : (a n i : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (Finset.dvd_gcd_iff.mp hpd i (Finset.mem_univ i))
  have hmod : X ^ N - C (v : ZMod p) ∣ (X - C (-(u : ZMod p))) ^ n := by
    simpa only [F, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_add, map_X, map_C,
      Polynomial.map_sum, Polynomial.map_mul, Int.coe_castRingHom, Int.cast_natCast, hcoeff,
      map_zero, zero_mul, Finset.sum_const_zero, sub_zero, map_neg, sub_neg_eq_add] using
      Polynomial.map_dvd (Int.castRingHom (ZMod p)) hdvd
  obtain hcop | hlin :=
    (irreducible_X_sub_C (-(u : ZMod p))).isCoprime_or_dvd (X ^ N - C (v : ZMod p))
  · have hunit := hcop.symm.pow_right.isUnit_of_dvd hmod
    exact (hN (by simpa only [natDegree_X_pow_sub_C] using natDegree_eq_zero_of_isUnit hunit)).elim
  · have hroot : (-(u : ZMod p)) ^ N = v := by
      simpa [IsRoot.def, sub_eq_zero] using dvd_iff_isRoot.mp hlin
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
    push_cast
    rw [← hroot, pow_succ, mul_right_comm, ← mul_pow]
    simp

end MetaMathlibExt
