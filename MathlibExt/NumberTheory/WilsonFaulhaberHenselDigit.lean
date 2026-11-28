/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.NumberTheory.FermatQuotient
import MathlibExt.NumberTheory.WilsonFermatQuotient
import Mathlib.Tactic.Ring

/-!
# The second Hensel digit in Wilson's congruence

## References

* Claire Levaillant, *Wilson's Theorem Modulo p^2 Derived from Faulhaber Polynomials*,
  INTEGERS 24 (2024), Article A87, pp. 1–17, Lemma 1 (§2, p. 5, equation (7)).
  <https://math.colgate.edu/~integers/y87/y87.pdf>
* Fernando Q. Gouvêa, *p-adic Numbers: An Introduction*, 2nd ed., Universitext,
  Springer-Verlag Berlin Heidelberg (1997), for the Hensel lifting used in the source.
  <https://doi.org/10.1007/978-3-642-59058-0>
-/

namespace MathlibExt.NumberTheory.WilsonFaulhaberWanted

/-- **Lemma 1**: for `1 ≤ k ≤ p - 1` let `k + p t` (with `t ∈ ℤ`) satisfy
`(k + p t)^(p-1) + (p - 1)! ≡ 0 (mod p^2)`, i.e. `t` reduces to the second
`p`-adic digit `t_k^{(0)}` of the Hensel root `x_k ≡ k (mod p)` of
`X^(p-1) + (p - 1)!`. Then `p t ≡ k (1 + (p - 1)! + p δ₀(k)) (mod p^2)`, with
`δ₀(k)` the Fermat quotient (`Int.fermatQuotient`).

Source: Claire Levaillant, *Wilson's Theorem Modulo p^2 Derived from Faulhaber
Polynomials*, INTEGERS 24 (2024), Article A87, Lemma 1. -/
public theorem hensel_digit_mul_prime_mod_sq (p : ℕ) (hp : p.Prime) (k : ℕ)
    (hk : k ∈ Finset.Icc 1 (p - 1)) (t : ℤ)
    (ht : (p : ℤ) ^ 2 ∣ ((k : ℤ) + p * t) ^ (p - 1) + (Nat.factorial (p - 1) : ℤ)) :
    (((p : ℤ) * t : ℤ) : ZMod (p ^ 2)) =
      (k : ZMod (p ^ 2)) * (1 + (Nat.factorial (p - 1) : ZMod (p ^ 2)) +
        (p : ZMod (p ^ 2)) *
          ((Int.fermatQuotient p hp (k : ℤ) (by exact isCoprime_intCast_of_mem_Icc hp hk) : ℤ) :
            ZMod (p ^ 2))) := by
  let P : ZMod (p ^ 2) := p
  let K : ZMod (p ^ 2) := k
  let T : ZMod (p ^ 2) := t
  let F : ZMod (p ^ 2) := Nat.factorial (p - 1)
  let Q : ZMod (p ^ 2) := Int.fermatQuotient p hp (k : ℤ) (isCoprime_intCast_of_mem_Icc hp hk)
  rw [Int.cast_mul, Int.cast_natCast]
  change P * T = K * (1 + F + P * Q)
  have hP : P * P = 0 := by
    calc
      _ = P ^ 2 := (pow_two P).symm
      _ = ((p ^ 2 : ℕ) : ZMod (p ^ 2)) := (Nat.cast_pow p 2).symm
      _ = 0 := ZMod.natCast_self _
  have hQ : K ^ (p - 1) = 1 + P * Q := by
    have h := congrArg (fun z : ℤ => (z : ZMod (p ^ 2)))
      (Int.natCast_mul_fermatQuotient p hp (k : ℤ) (isCoprime_intCast_of_mem_Icc hp hk))
    have h' : P * Q = K ^ (p - 1) - 1 := by
      simpa only [P, K, Q, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
        Int.cast_one] using h
    rw [h']
    ring
  -- The Fermat congruence still holds modulo `p ^ 2` after multiplying by `p`.
  have hscale : P * K ^ (p - 1) = P := by
    rw [hQ, mul_add, mul_one, ← mul_assoc, hP, zero_mul, add_zero]
  let D := K ^ (p - 2)
  have hD : K * D = K ^ (p - 1) := by
    change K * K ^ (p - 2) = _
    rw [← pow_succ', show p - 2 + 1 = p - 1 by have := hp.two_le; omega]
  have hfactor : K + P * T = K * (1 + P * (T * D)) := by
    calc
      _ = K + (P * (K * D)) * T := by rw [hD, hscale]
      _ = _ := by ring
  have hlinear := prod_one_add_mul_of_square_zero P hP (Finset.range (p - 1)) (fun _ ↦ T * D)
  simp only [Finset.prod_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlinear
  have hpow : (K + P * T) ^ (p - 1) = K ^ (p - 1) + (P - 1) * (P * T) * D := by
    rw [hfactor, mul_pow, hlinear, Nat.cast_sub hp.one_le, Nat.cast_one]
    calc
      _ = K ^ (p - 1) + (P * K ^ (p - 1)) * ((P - 1) * T * D) := by ring
      _ = _ := by rw [hscale]; ring
  have hroot : (K + P * T) ^ (p - 1) + F = 0 := by
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ 2)).mpr
      (by simpa only [Nat.cast_pow] using ht)
    simpa only [K, P, T, F, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast] using hz
  have hcoeff : (P - 1) * P * T = -(P * T) := by
    calc
      _ = (P * P) * T - P * T := by ring
      _ = _ := by rw [hP, zero_mul, zero_sub]
  have hzero : K * (1 + F + P * Q) - P * T = 0 := by
    calc
      _ = K * (K ^ (p - 1) + F) + (P - 1) * P * T := by
        rw [hQ, hcoeff]
        ring
      _ = K * ((K + P * T) ^ (p - 1) + F) := by
        rw [hpow]
        calc
          _ = K * (K ^ (p - 1) + F) + (P - 1) * (P * (K * D)) * T := by
            rw [hD, hscale]
          _ = _ := by ring
      _ = 0 := by rw [hroot, mul_zero]
  exact (sub_eq_zero.mp hzero).symm

end MathlibExt.NumberTheory.WilsonFaulhaberWanted
