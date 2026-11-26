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
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.FieldTheory.KummerPolynomial
import MathlibExt.NumberTheory.GcdPowAddNegOnePow
import MathlibExt.NumberTheory.PrimeDvdPowAddOfDvdRadicalCoeffsGcd

/-!
# Coprime radical-expansion coefficients

The integer coefficients of every positive power of `u + v^{1/N}` have greatest common
divisor one when `N` has two distinct prime divisors, `u` and `v` are coprime and positive,
and `X ^ N - v` is irreducible over the rationals.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Theorem 16 and its
unnumbered restatement in the introduction.
-/

namespace MetaMathlibExt

open Polynomial

/-- **Coprime coefficients of $(u + v^{1/N})^n$ when $N$ has two distinct prime factors.** Let
$N$ be a natural number with at least two distinct prime divisors, let $u, v$ be coprime positive
integers such that $x^N - v$ is irreducible over $\mathbb{Q}$, let $\theta = v^{1/N}$ be the
positive real $N$-th root of $v$, and let $a_{n,i}$ (for natural $n$ and $0 \le i \le N - 1$) be
integers with $(u + \theta)^n = \sum_{i=0}^{N-1} a_{n,i} \theta^i$ for every $n \ge 1$. Then for
every $n \ge 1$ the greatest common divisor of $a_{n,0}, \dots, a_{n,N-1}$ is $1$.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Theorem 16
(`jis-2025-25.2.2-thm-16`) and its unnumbered restatement in the introduction
(`jis-2025-25.2.2-thm-unnumbered-1`). -/
public theorem gcd_radical_expansion_coeffs_eq_one {N u v : ℕ}
    (hN : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ N ∧ q ∣ N) (hu : 0 < u) (hv : 0 < v)
    (huv : u.Coprime v)
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (a : ℕ → Fin N → ℤ)
    (ha : ∀ n, 1 ≤ n → ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a n i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ))
    (n : ℕ) (hn : 1 ≤ n) :
    Finset.univ.gcd (a n) = 1 := by
  classical
  have hN0 := ne_zero_of_irreducible_X_pow_sub_C hirr
  rw [← Finset.normalize_gcd, normalize_eq_one, Int.isUnit_iff_natAbs_eq]
  by_contra hd
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
  have hpd' : (p : ℤ) ∣ Finset.univ.gcd (a n) := Int.natCast_dvd.mpr hpd
  have hnorm := prime_dvd_pow_add_of_dvd_radical_coeffs_gcd hirr a ha n hn p hp hpd'
  have hcop := (gcd_pow_add_neg_one_pow_mul_eq_one (Nat.one_le_iff_ne_zero.mpr hN0)
    hu hv huv).1
  have hpu : ¬p ∣ u := by
    intro hpu
    exact hp.not_dvd_one (hcop ▸ Int.dvd_gcd hnorm (Int.natCast_dvd_natCast.mpr hpu))
  let : Fact p.Prime := ⟨hp⟩
  have hu0 : (u : ZMod p) ≠ 0 := by
    exact fun h ↦ hpu ((ZMod.natCast_eq_zero_iff u p).mp h)
  let θ := (v : ℝ) ^ (1 / (N : ℝ))
  have hθ : θ ^ N = v := by
    simpa only [θ, one_div] using Real.rpow_inv_natCast_pow (Nat.cast_nonneg v) hN0
  have hmin : X ^ N - C (v : ℚ) = minpoly ℚ θ :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hθ]) (monic_X_pow_sub_C _ hN0)
  let F : ℤ[X] := (X + C (u : ℤ)) ^ n - ∑ i : Fin N, C (a n i) * X ^ (i : ℕ)
  have hdvd : X ^ N - C (v : ℤ) ∣ F := by
    apply (map_dvd_map (Int.castRingHom ℚ) Int.cast_injective (monic_X_pow_sub_C _ hN0)).mp
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, map_natCast, hmin]
    apply minpoly.dvd ℚ θ
    simpa [F, Polynomial.map_sum, θ, add_comm (u : ℝ), sub_eq_zero] using ha n hn
  have hcoeff (i : Fin N) : (a n i : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (Finset.dvd_gcd_iff.mp hpd' i (Finset.mem_univ i))
  have hmod : X ^ N - C (v : ZMod p) ∣ (X + C (u : ZMod p)) ^ n := by
    simpa only [F, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_add, map_X, map_C,
      Polynomial.map_sum, Polynomial.map_mul, Int.coe_castRingHom, Int.cast_natCast, hcoeff,
      map_zero, zero_mul, Finset.sum_const_zero, sub_zero] using
      Polynomial.map_dvd (Int.castRingHom (ZMod p)) hdvd
  have hprime : Prime (X + C (u : ZMod p)) := by
    simpa only [map_neg, sub_neg_eq_add] using (irreducible_X_sub_C (-(u : ZMod p))).prime
  obtain ⟨k, -, hk⟩ := (dvd_prime_pow hprime n).mp hmod
  have heq : X ^ N - C (v : ZMod p) = (X + C (u : ZMod p)) ^ k :=
    eq_of_monic_of_associated (monic_X_pow_sub_C _ hN0) ((monic_X_add_C _).pow _) hk
  have hNk : N = k := by
    simpa only [natDegree_X_pow_sub_C, natDegree_pow_X_add_C] using congrArg natDegree heq
  subst k
  have hchoose : ∀ i ∈ Finset.Icc 1 (N - 1), N.choose i ≡ 0 [MOD p] := by
    intro i hi
    have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
    have hiN : i ≠ N := by have := (Finset.mem_Icc.mp hi).2; omega
    have h := congrArg (fun f : (ZMod p)[X] ↦ f.coeff i) heq
    have hmul : (u : ZMod p) ^ (N - i) * (N.choose i : ZMod p) = 0 := by
      simpa only [coeff_sub, coeff_X_pow, coeff_C, ite_eq_right hiN.symm,
        ite_eq_right hiN, ite_eq_right hi0,
        sub_self, coeff_X_add_C_pow] using h.symm
    exact Nat.modEq_zero_iff_dvd.mpr ((ZMod.natCast_eq_zero_iff _ _).mp
      ((mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hu0)))
  have hpow := Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat
    (Nat.pos_of_ne_zero hN0) hchoose
  obtain ⟨q, r, hq, hr, hqr, hqN, hrN⟩ := hN
  have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp
    (hq.dvd_of_dvd_pow (hpow ▸ hqN))
  have hrp : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp
    (hr.dvd_of_dvd_pow (hpow ▸ hrN))
  exact hqr (hqp.trans hrp.symm)

end MetaMathlibExt
