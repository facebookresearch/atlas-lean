/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Finite.PermutationPolynomial
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Monomial permutation polynomials of a finite field

The main result, `MetaMathlibExt.isPermutationPolynomial_X_pow_iff_coprime`, says that for a
finite field `K` with `q` elements and an integer `d ≥ 1`, the monomial `X ^ d` is a permutation
polynomial of `K` if and only if `gcd(d, q - 1) = 1`.

The unit group `Kˣ` has order `q - 1`. If `d` is coprime to `q - 1`, then `x ↦ x ^ d` is a
bijection of `Kˣ`, and it fixes `0`. Conversely, a prime `p` dividing both `d` and `q - 1` gives,
by Cauchy's theorem, a unit `ζ` of order `p`, so `ζ ≠ 1` and `ζ ^ d = 1 = 1 ^ d`.
-/

namespace MetaMathlibExt

open Polynomial

/-- **Monomial permutation polynomials of a finite field.** Let $K$ be a finite field with $q$
elements and let $d \ge 1$ be an integer. Then $X^d$ is a permutation polynomial of $K$ if and
only if $\gcd(d, q - 1) = 1$.

The hypothesis $d \ge 1$ is needed: for $d = 0$ and $q = 2$ the condition $\gcd(d, q - 1) = 1$
holds, but $X^0 = 1$ is constant.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Lemma 2
(`integers-2024-A12-lem-2`). -/
public theorem isPermutationPolynomial_X_pow_iff_coprime {K : Type*} [Field K]
    [Fintype K] {d : ℕ} (hd : 0 < d) :
    (X ^ d : K[X]).IsPermutationPolynomial ↔ d.Coprime (Fintype.card K - 1) := by
  have hcard : Nat.card Kˣ = Fintype.card K - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
  simp only [Polynomial.IsPermutationPolynomial, eval_pow, eval_X,
    ← Finite.injective_iff_bijective]
  constructor
  · intro hinj
    by_contra hcop
    obtain ⟨p, hp, hpd, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (hcard ▸ hpq)
    have hζd : ζ ^ d = 1 := orderOf_dvd_iff_pow_eq_one.mp (hζ ▸ hpd)
    have hζ1 : ζ = 1 := Units.ext <| hinj <| by
      change (ζ : K) ^ d = ((1 : Kˣ) : K) ^ d
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hζd, one_pow]
    exact hp.one_lt.ne' (by rw [← hζ, hζ1, orderOf_one])
  · intro hcop x y hxy
    simp only at hxy
    have hbij := Nat.Coprime.pow_left_bijective (G := Kˣ) (n := d) (hcard ▸ hcop.symm)
    rcases eq_or_ne x 0 with rfl | hx
    · rw [zero_pow hd.ne'] at hxy
      exact ((pow_eq_zero_iff hd.ne').mp hxy.symm).symm
    rcases eq_or_ne y 0 with rfl | hy
    · rw [zero_pow hd.ne'] at hxy
      exact (pow_eq_zero_iff hd.ne').mp hxy
    have hunits := hbij.1 (a₁ := Units.mk0 x hx) (a₂ := Units.mk0 y hy) (Units.ext <| by
      simpa using hxy)
    simpa using congrArg Units.val hunits

end MetaMathlibExt
