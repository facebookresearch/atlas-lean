/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Data.ZMod.Coprime
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Finite.Basic
public import MathlibExt.NumberTheory.LehmerCompanionMersenneDivisibility

/-!
# Lehmer's companion sequence as a Mersenne primality test

For odd $n \ge 3$ and integers $R,Q$ with $\gcd(2^n-1,Q)=1$, divisibility of
$\bar V_{2^{n-1}}(R,Q)$ by $2^n-1$ implies that $2^n-1$ is prime. This also permits noncoprime
$R,Q$: only $Q$ must be nonzero modulo each prime divisor of $2^n-1$.

The proof works over the algebraic closure of the residue field of a prime divisor. The vanishing
companion term forces a root of a reciprocal quadratic to have order $2^n$. Frobenius preserves
the two roots, so this order divides either one less or one more than the prime divisor.

## References

* E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality Test*,
  Journal of Integer Sequences **28** (2025), Article 25.2.5, pp. 1–26, §2 (recurrence (2) and
  Lemma 4). <https://cs.uwaterloo.ca/journals/JIS/VOL28/Roettger/roettger15.pdf>
* D. H. Lehmer, *An Extended Theory of Lucas' Functions*, Annals of Mathematics **31** (1930),
  pp. 419–448, §1 and Theorems 1.8 and 1.9 (the rank-of-appearance results behind Lemma 4).
* The induction on the even subsequence follows `lehmerV_even_eq_chebyshev` in
  `MathlibExt.NumberTheory.LehmerCompanionMersenneDivisibility`, using a sum of powers in place
  of a Chebyshev evaluation.
-/

namespace MetaMathlibExt

open Polynomial

private theorem intCast_lehmerV_even_eq_sum_powers {K : Type*} [CommRing K] (R Q : ℤ)
    (a b : K) (hs : a + b = (R : K) - 2 * Q) (hp : a * b = (Q : K) ^ 2) (k : ℕ) :
    (lehmerV R Q (2 * k) : K) = a ^ k + b ^ k := by
  induction k using Nat.twoStepInduction with
  | zero => norm_num [lehmerV.eq_1]
  | one => simpa only [mul_one, lehmerV.eq_3, Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
      pow_one] using hs.symm
  | more k ih₀ ih₁ =>
      rw [show 2 * (k + 2) = 2 * k + 4 by omega, lehmerV_add_four]
      push_cast
      rw [show 2 * k + 2 = 2 * (k + 1) by omega, ih₀, ih₁, ← hs, ← hp]
      ring

/-- **Lehmer-sequence primality criterion for Mersenne numbers.** Let $n \ge 3$ be odd, let
$M_n = 2^n - 1$, and let $R$ and $Q$ be integers with $\gcd(M_n, Q) = 1$. If $M_n$ divides
Lehmer's companion term $\bar V_{2^{n-1}}(R, Q)$, then $M_n$ is prime.

Here $2^{n-1} = (M_n + 1)/2$. No coprimality of $R$ and $Q$ and no condition on $D = R - 4Q$
is assumed.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Lemma 4. -/
public theorem mersenne_prime_of_dvd_lehmerV {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n)
    (R Q : ℤ) (hQ : Int.gcd (mersenne n) Q = 1)
    (hV : (mersenne n : ℤ) ∣ lehmerV R Q (2 ^ (n - 1))) :
    (mersenne n).Prime := by
  let p := (mersenne n).minFac
  have hM : 1 < mersenne n := one_lt_mersenne.mpr (by omega)
  have hp : p.Prime := Nat.minFac_prime hM.ne'
  have hpd : p ∣ mersenne n := Nat.minFac_dvd _
  have hp2 : 2 < p := by
    refine lt_of_le_of_ne hp.two_le ?_
    intro he
    exact (mersenne_odd.mpr (by rintro rfl; simp at hn)).not_two_dvd_nat (he.symm ▸ hpd)
  have hpd' : (p : ℤ) ∣ (mersenne n : ℤ) := Int.natCast_dvd_natCast.mpr hpd
  let : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  let ι : ZMod p →+* K := algebraMap _ _
  let : CharP K p := charP_of_injective_ringHom ι.injective p
  have hcop : IsCoprime (p : ℤ) Q :=
    (Int.isCoprime_iff_gcd_eq_one.mpr hQ).of_isCoprime_of_dvd_left hpd'
  have hQp : (Q : ZMod p) ≠ 0 :=
    ZMod.ne_zero_of_gcd_eq_one hp (Int.isCoprime_iff_gcd_eq_one.mp hcop.symm)
  have hQK : (Q : K) ≠ 0 := by
    simpa only [map_intCast] using (_root_.map_ne_zero ι).2 hQp
  have hzero : (lehmerV R Q (2 ^ (n - 1)) : K) = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hpd'.trans hV)
    simpa only [map_intCast, map_zero] using congrArg ι h
  -- Normalize the characteristic polynomial of the even subsequence to constant term 1.
  let s : ZMod p := ((R : ZMod p) - 2 * Q) / Q
  have hs : ι s * (Q : K) = (R : K) - 2 * Q := by
    simpa only [map_mul, map_sub, map_intCast, map_ofNat] using
      congrArg ι (div_mul_cancel₀ ((R : ZMod p) - 2 * Q) hQp)
  let f : K[X] := C 1 * X ^ 2 + C (-(ι s)) * X + C 1
  have hf : f.degree ≠ 0 := by
    dsimp only [f]
    rw [degree_quadratic one_ne_zero]
    decide
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root f hf
  have hu' : u ^ 2 - ι s * u + 1 = 0 := by
    simpa [IsRoot, f, sub_eq_add_neg] using hu
  let v := ι s - u
  have huv : u * v = 1 := by dsimp [v]; linear_combination -hu'
  have hu0 : u ≠ 0 := by rintro rfl; simp at huv
  have hsum : u + v = ι s := by dsimp [v]; ring
  let k := 2 ^ (n - 2)
  have hidx : 2 ^ (n - 1) = 2 * k := by
    dsimp [k]
    rw [show n - 1 = n - 2 + 1 by omega, pow_succ']
  have htrace : u ^ k + v ^ k = 0 := by
    rw [hidx, intCast_lehmerV_even_eq_sum_powers R Q ((Q : K) * u) ((Q : K) * v)] at hzero
    · simp only [mul_pow, ← mul_add] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hQK)
    · rw [← mul_add, hsum, mul_comm, hs]
    · calc
        _ = (Q : K) ^ 2 * (u * v) := by ring
        _ = _ := by rw [huv, mul_one]
  -- The vanishing trace and the reciprocal product give exact order `2 ^ n`.
  have hminus : u ^ (2 ^ (n - 1)) = -1 := by
    have hprod : u ^ k * v ^ k = 1 := by rw [← mul_pow, huv, one_pow]
    rw [hidx, Nat.mul_comm 2, pow_mul, pow_two]
    linear_combination u ^ k * htrace - hprod
  have hneg : (-1 : K) ≠ 1 := by
    intro he
    have htwo : (2 : K) = 0 := by linear_combination -he
    exact (Nat.not_dvd_of_pos_of_lt (by decide) hp2) ((CharP.cast_eq_zero_iff K p 2).mp htwo)
  have horder : orderOf u = 2 ^ n := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have horder := orderOf_eq_prime_pow (p := 2) (n := n - 1)
      (hminus ▸ hneg) (by rw [pow_succ, pow_mul, hminus]; norm_num)
    rwa [show n - 1 + 1 = n by omega] at horder
  -- Frobenius fixes the coefficient in the prime field, so `u ^ p` is one of the two roots.
  have hfix : frobenius K p (ι s) = ι s := by
    rw [← ι.map_frobenius, ZMod.frobenius_zmod, RingHom.id_apply]
  have hroot : (u ^ p) ^ 2 - ι s * u ^ p + 1 = 0 := by
    simpa only [map_add, map_sub, map_mul, map_pow, map_one, map_zero, hfix, frobenius_def] using
      congrArg (frobenius K p) hu'
  have hfactor : (u ^ p - u) * (u ^ p - v) = 0 := by
    linear_combination hroot - u ^ p * hsum + huv
  have hle : 2 ^ n ≤ p + 1 := by
    rw [← horder]
    rcases (mul_eq_zero.mp hfactor).imp sub_eq_zero.mp sub_eq_zero.mp with he | he
    · have he' : u ^ (p - 1) = 1 := by
        apply mul_right_cancel₀ hu0
        rw [← pow_succ, show p - 1 + 1 = p by omega, he, one_mul]
      exact (orderOf_le_of_pow_eq_one (by omega) he').trans (by omega)
    · have he' : u ^ (p + 1) = 1 := by rw [pow_succ, he, mul_comm, huv]
      exact orderOf_le_of_pow_eq_one (by omega) he'
  rw [← succ_mersenne] at hle
  have heq : p = mersenne n := le_antisymm (Nat.le_of_dvd (by omega) hpd) (by omega)
  exact heq ▸ hp

end MetaMathlibExt
