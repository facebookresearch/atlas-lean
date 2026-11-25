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
# Common prime divisors of the radical norm and coefficient gcd

Modulo a prime dividing the coefficient gcd, the defining binomial divides a power of `X + u`.
Monicity and degree identify the binomial with `(X + u)^N`. Comparing the next-to-leading
coefficients gives `N * u = 0` modulo the prime.
-/

namespace MetaMathlibExt

open Polynomial

/-- **Common prime factors of $u^N + (-1)^{N+1} v$ and the coefficient gcd divide $N$.** Let
$N \ge 2$, let $u, v$ be coprime natural numbers such that $x^N - v$ is irreducible over
$\mathbb{Q}$, let $\theta = v^{1/N}$ be the nonnegative real $N$-th root of $v$, and let $a_{n,i}$
(for natural $n$ and $0 \le i \le N - 1$) be integers with
$(u + \theta)^n = \sum_{i=0}^{N-1} a_{n,i} \theta^i$ for every $n \ge 1$. Write $D_n$ for the
nonnegative greatest common divisor of $a_{n,0}, \dots, a_{n,N-1}$. Then for every $n \ge 1$,
every prime $p$ dividing $\gcd(u^N + (-1)^{N+1} v, D_n)$ divides $N$.

The paper assumes $N \ge 4$; the cases $N = 2, 3$ also hold, while $N = 1$ fails, since then
$D_n = (u + v)^n$.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Lemma 6
(`jis-2025-25.2.2-lem-6`). -/
public theorem prime_dvd_gcd_pow_add_radical_coeffs {N u v : ℕ} (hN : 2 ≤ N)
    (huv : u.Coprime v)
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (a : ℕ → Fin N → ℤ)
    (ha : ∀ n, 1 ≤ n → ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a n i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ))
    (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime)
    (hpd : (p : ℤ) ∣ GCDMonoid.gcd ((u : ℤ) ^ N + (-1) ^ (N + 1) * v) (Finset.univ.gcd (a n))) :
    p ∣ N := by
  obtain ⟨hnorm, hgcd⟩ := (dvd_gcd_iff ..).mp hpd
  have hN0 : N ≠ 0 := by omega
  let θ := (v : ℝ) ^ (1 / (N : ℝ))
  have hθ : θ ^ N = v := by
    simpa only [θ, one_div] using Real.rpow_inv_natCast_pow (Nat.cast_nonneg v) hN0
  have hmin : X ^ N - C (v : ℚ) = minpoly ℚ θ :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hθ]) (monic_X_pow_sub_C _ hN0)
  -- As in the radical norm divisibility proof, descend from ℚ to ℤ by monicity.
  let F : ℤ[X] := (X + C (u : ℤ)) ^ n - ∑ i : Fin N, C (a n i) * X ^ (i : ℕ)
  have hdvd : X ^ N - C (v : ℤ) ∣ F := by
    apply (map_dvd_map (Int.castRingHom ℚ) Int.cast_injective (monic_X_pow_sub_C _ hN0)).mp
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, map_natCast, hmin]
    apply minpoly.dvd ℚ θ
    simpa [F, Polynomial.map_sum, θ, add_comm (u : ℝ), sub_eq_zero] using ha n hn
  let : Fact p.Prime := ⟨hp⟩
  have hcoeff (i : Fin N) : (a n i : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (Finset.dvd_gcd_iff.mp hgcd i (Finset.mem_univ i))
  have hmod : X ^ N - C (v : ZMod p) ∣ (X + C (u : ZMod p)) ^ n := by
    simpa only [F, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_add, map_X, map_C,
      Polynomial.map_sum, Polynomial.map_mul, Int.coe_castRingHom, Int.cast_natCast, hcoeff,
      map_zero, zero_mul, Finset.sum_const_zero, sub_zero] using
      Polynomial.map_dvd (Int.castRingHom (ZMod p)) hdvd
  -- A monic divisor of a power of a prime linear polynomial is itself a power of it.
  have hprime : Prime (X + C (u : ZMod p)) := by
    simpa only [map_neg, sub_neg_eq_add] using (irreducible_X_sub_C (-(u : ZMod p))).prime
  obtain ⟨k, -, hk⟩ := (dvd_prime_pow hprime n).mp hmod
  have heq : X ^ N - C (v : ZMod p) = (X + C (u : ZMod p)) ^ k :=
    eq_of_monic_of_associated (monic_X_pow_sub_C _ hN0) ((monic_X_add_C _).pow _) hk
  have hNk : N = k := by
    simpa only [natDegree_X_pow_sub_C, natDegree_pow_X_add_C] using congrArg natDegree heq
  subst k
  have hchoose : N.choose (N - 1) = N := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ N)] using Nat.choose_succ_self_right (N - 1)
  have hmul : (u : ZMod p) * (N : ZMod p) = 0 := by
    have h := congrArg (fun f : (ZMod p)[X] ↦ f.coeff (N - 1)) heq
    simpa only [coeff_sub, coeff_X_pow, coeff_C, ite_eq_right (show N ≠ N - 1 by omega),
      ite_eq_right (show N - 1 ≠ N by omega), ite_eq_right (show N - 1 ≠ 0 by omega), sub_self,
      coeff_X_add_C_pow, hchoose, show N - (N - 1) = 1 by omega, pow_one] using h.symm
  -- A zero residue for u would force v to have zero residue as well, by the norm hypothesis.
  have hu : (u : ZMod p) ≠ 0 := by
    intro hu0
    have hnorm0 : (u : ZMod p) ^ N + (-1) ^ (N + 1) * (v : ZMod p) = 0 := by
      simpa only [Int.cast_add, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_mul,
        Int.cast_natCast] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hnorm
    rw [hu0, zero_pow hN0, zero_add] at hnorm0
    have hv0 := (mul_eq_zero.mp hnorm0).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    have hpu := (ZMod.natCast_eq_zero_iff u p).mp hu0
    have hpv := (ZMod.natCast_eq_zero_iff v p).mp hv0
    exact hp.not_dvd_one (huv.gcd_eq_one ▸ Nat.dvd_gcd hpu hpv)
  exact (ZMod.natCast_eq_zero_iff N p).mp ((mul_eq_zero.mp hmul).resolve_left hu)

end MetaMathlibExt
