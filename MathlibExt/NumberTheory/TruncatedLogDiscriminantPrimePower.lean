/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TruncatedLogResultantPrimePower
import all MathlibExt.NumberTheory.TruncatedLogDiscriminant
import MathlibExt.NumberTheory.TruncatedLogResultantPos
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Truncated logarithmic discriminants at prime powers

For degrees congruent to one modulo four, clearing the discriminant formula's
square denominator reduces the question to the degree times the resultant product.

## References

* John Cullinan and Rylan Gajek-Leonard, *On the Discriminants of Truncated
  Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, pp. 1–12;
  Equation (6), Lemma 1, Theorem 4 and Corollary 1.
-/

namespace MetaMathlibExt

open Polynomial

open not_isSquare_discr_truncatedLog_three_five_seven_mul in
private theorem discr_mul_lcm_of_mod_four {n : ℕ} (hn : n % 4 = 1) :
    (truncatedLogPolynomial n).discr * (truncatedLogLcm n : ℚ) ^ (n - 1) =
      (n : ℚ) * (truncatedLogResultantProduct n : ℚ) := by
  have hsign : Even (n * (n - 1) / 2) := by
    rw [Nat.mul_div_assoc _ (show 2 ∣ n - 1 by omega)]
    exact (show Even ((n - 1) / 2) from ⟨n / 4, by omega⟩).mul_left n
  simpa [signedProduct, hsign.neg_one_pow] using discr_mul_lcm (show 0 < n by omega)

private theorem isSquare_mul_right_iff {x y : ℚ} (hy : IsSquare y) (hy0 : y ≠ 0) :
    IsSquare (x * y) ↔ IsSquare x :=
  ⟨fun h ↦ by simpa only [mul_div_cancel_right₀ _ hy0] using h.div hy, fun h ↦ h.mul hy⟩

/-- **Discriminants of $F_{p^e}$ for primes $p \equiv 1 \pmod 4$.** Let $p$ be a prime with
$p \equiv 1 \pmod 4$, let $e \ge 1$, let $F_n(x) = 1 + x + x^2/2 + \cdots + x^n/n$ be the
truncated logarithmic polynomial and let $\mathcal{P}_n$ be the truncated logarithmic resultant
product. If $e$ is odd, the discriminant of $F_{p^e}$ is not a square in $\mathbb{Q}$. If $e$ is
even, the discriminant of $F_{p^e}$ is not a square in $\mathbb{Q}$ if and only if the integer
$\mathcal{P}_{p^e}$ is not a square in $\mathbb{Q}$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Corollary 1
(`integers-2025-A39-cor-1`). -/
public theorem discr_truncatedLog_prime_power {p e : ℕ} (hp : p.Prime)
    (hp4 : p % 4 = 1) (he : 1 ≤ e) :
    (Odd e → ¬ IsSquare (truncatedLogPolynomial (p ^ e)).discr) ∧
      (Even e → (¬ IsSquare (truncatedLogPolynomial (p ^ e)).discr ↔
        ¬ IsSquare ((truncatedLogResultantProduct (p ^ e) : ℤ) : ℚ))) := by
  have hmod : p ^ e % 4 = 1 := by
    rw [Nat.pow_mod, hp4, one_pow]
    decide
  have hL : (truncatedLogLcm (p ^ e) : ℚ) ^ (p ^ e - 1) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast Nat.lcmUpto_ne_zero (p ^ e))
  have hEven : Even (p ^ e - 1) := ⟨(p ^ e - 1) / 2, by omega⟩
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hdiscr := discr_mul_lcm_of_mod_four hmod
  have hsquare : IsSquare (truncatedLogPolynomial (p ^ e)).discr ↔
      IsSquare ((p : ℚ) ^ e * (truncatedLogResultantProduct (p ^ e) : ℚ)) := by
    rw [← Nat.cast_pow, ← hdiscr]
    exact (isSquare_mul_right_iff (hEven.isSquare_pow _) hL).symm
  constructor
  · intro hOdd hs
    -- The cleared product has p-adic valuation e, whereas a square has even valuation.
    let _ : Fact p.Prime := ⟨hp⟩
    have hP : (truncatedLogResultantProduct (p ^ e) : ℚ) ≠ 0 := by
      exact_mod_cast (truncatedLogResultantProduct_pos (pow_pos hp.pos e)).ne'
    have hPval : padicValRat p (truncatedLogResultantProduct (p ^ e) : ℚ) = 0 := by
      rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd
        (not_dvd_truncatedLogResultantProduct_of_prime_power hp hp4 he), Nat.cast_zero]
    have hv : padicValRat p ((p : ℚ) ^ e * (truncatedLogResultantProduct (p ^ e) : ℚ)) = e := by
      rw [padicValRat.mul (pow_ne_zero _ hpQ) hP, padicValRat.pow, padicValRat.self hp.one_lt,
        hPval, mul_one, add_zero]
    obtain ⟨r, hr⟩ := hsquare.mp hs
    rw [hr, ← pow_two, padicValRat.pow] at hv
    obtain ⟨k, hk⟩ := hOdd
    omega
  · intro heven
    rw [hsquare, mul_comm, isSquare_mul_right_iff (heven.isSquare_pow _) (pow_ne_zero _ hpQ)]

end MetaMathlibExt
