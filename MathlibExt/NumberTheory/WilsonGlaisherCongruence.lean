/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Padics.PadicNorm

import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Bernoulli.TruncatedSumModPrime
import MathlibExt.NumberTheory.WilsonFermatQuotient

/-!
# Glaisher's congruence for Wilson's theorem modulo `p^2`

For each prime `p`, `(p - 1)!` is congruent to `p B_(p-1) - p` modulo `p^2` in the
rational `p`-adic norm, using `B₁ = -1/2`. For odd `p`, multiply the congruence by
`p` and expand the power sum up to `p - 1` by evaluating Faulhaber's formula at `p`.
The terms other than `p^2 B_(p-1)` are multiples of `p^3` with `p`-integral quotients.
At `p = 2`, the difference is exactly `4`.

## References

* Claire Levaillant, *Wilson's Theorem Modulo p^2 Derived from Faulhaber Polynomials*,
  INTEGERS 24 (2024), Article A87, pp. 1–17, Corollary 1 (p. 4) and the alternative proof
  on p. 9, equations (20)–(22). <https://math.colgate.edu/~integers/y87/y87.pdf>
* J. W. L. Glaisher, *On the residues of the sums of products of the first p − 1 numbers and
  their powers, to modulus p^2 or p^3*, Quart. J. Math. 31 (1900), pp. 321–353
  (the original congruence).
* Z-H. Sun, *Congruences concerning Bernoulli numbers and Bernoulli polynomials*,
  Discrete Applied Mathematics 105 (2000), pp. 193–223 (the power-sum reduction to evaluation
  at `p`, credited to Sun by Levaillant before equation (21)).
* The alternative proof cites von Staudt–Clausen for the denominators: T. Clausen, *Theorem*,
  Astronomische Nachrichten 17, no. 22 (1840), pp. 351–352, and C. von Staudt,
  *Beweis eines Lehrsatzes, die Bernoullischen Zahlen betreffend*, Journal für die reine und
  angewandte Mathematik 21 (1840), pp. 372–374. Here only the short-range integrality result
  `MetaMathlibExt.padicValuation_bernoulli'_le_one` from
  `MathlibExt.NumberTheory.Bernoulli.TruncatedSumModPrime` is needed.
* The modular factorial step uses `wilson_mod_prime_sq` from
  `MathlibExt.NumberTheory.WilsonFermatQuotient` (Levaillant's Theorem 1).
-/

set_option autoImplicit false

open Finset

namespace MathlibExt.NumberTheory.WilsonFaulhaberWanted

/-- **Corollary 1** (Glaisher): `(p - 1)! ≡ p B_{p-1} - p (mod p^2)`, read in `ℚ`
through the `p`-adic norm (`p B_{p-1}` is `p`-integral by von Staudt–Clausen).
Stated for every prime with Mathlib's `bernoulli` (`B₁ = -1/2`); at `p = 2` the
paper's second-type `B₁ = 1/2` would give `1 ≢ -1 (mod 4)`.

Source: Claire Levaillant, *Wilson's Theorem Modulo p^2 Derived from Faulhaber
Polynomials*, INTEGERS 24 (2024), Article A87, Corollary 1 (after Glaisher). -/
public theorem wilson_mod_prime_sq_bernoulli (p : ℕ) (hp : p.Prime) :
    padicNorm p ((Nat.factorial (p - 1) : ℚ) - (p * bernoulli (p - 1) - p)) ≤
      (p : ℚ) ^ (-2 : ℤ) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst p
    simp only [Nat.cast_ofNat]
    rw [show (Nat.factorial (2 - 1) : ℚ) - (2 * bernoulli (2 - 1) - 2) = ((4 : ℤ) : ℚ) by
      norm_num [bernoulli_one, Nat.factorial_succ]]
    exact (padicNorm.dvd_iff_norm_le (p := 2) (n := 2)).mp (by decide)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hsucc : p - 1 + 1 = p := by omega
  have hinterval : Icc 1 (p - 1) = Ico 1 p := by rw [← Ico_add_one_right_eq_Icc, hsucc]
  -- Eliminate the Fermat quotients before taking the integral lift.
  let S : ℤ := ∑ k ∈ range p, (k : ℤ) ^ (p - 1)
  obtain ⟨w, hw⟩ : (↑(p ^ 2 : ℕ) : ℤ) ∣ (Nat.factorial (p - 1) : ℤ) + p - S := by
    let R := ZMod (p ^ 2)
    have hsum : ∑ k ∈ Icc 1 (p - 1), (k : R) ^ (p - 1) = (S : R) := by
      rw [hinterval, sum_Ico_eq_sub _ hp.one_le]
      simp [S, zero_pow (Nat.sub_ne_zero_of_lt hp.one_lt)]
    have h := wilson_mod_prime_sq p hp hp2
    rw [mul_sum] at h
    conv at h =>
      rhs
      arg 2
      enter [2, k]
      rw [← Int.cast_natCast, ← Int.cast_mul, Int.natCast_mul_fermatQuotient, Int.cast_sub,
        Int.cast_pow, Int.cast_natCast, Int.cast_one]
    rw [sum_attach (f := fun k : ℕ => (k : R) ^ (p - 1) - 1), sum_sub_distrib,
      sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, hsum] at h
    rw [show p - 1 + 1 - 1 = p - 1 by omega, Nat.cast_sub hp.one_le, Nat.cast_one] at h
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [h]
    ring
  have hW : (Nat.factorial (p - 1) : ℚ) + p - (∑ k ∈ range p, (k : ℚ) ^ (p - 1)) =
      (p : ℚ) ^ 2 * (w : ℚ) := by
    simpa only [S, Int.cast_sub, Int.cast_add, Int.cast_sum, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast, Nat.cast_pow] using congrArg (fun n : ℤ => (n : ℚ)) hw
  -- After multiplying by `p`, the binomial coefficients supply the third factor of `p`.
  let c (j : ℕ) : ℕ := p.choose j * p ^ (p - j - 2) / p
  have hc (j : ℕ) (hj : j < p - 1) : p * c j = p.choose j * p ^ (p - j - 2) := by
    apply Nat.mul_div_cancel'
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp only [Nat.choose_zero_right, one_mul, Nat.sub_zero]
      exact dvd_pow_self _ (by omega)
    · exact dvd_mul_of_dvd_left (hp.dvd_choose_self hj0.ne' (by omega)) _
  let t (j : ℕ) := bernoulli j * (p.choose j : ℚ) * (p : ℚ) ^ (p - j)
  have hF : (p : ℚ) * (∑ k ∈ range p, (k : ℚ) ^ (p - 1)) = ∑ j ∈ range p, t j := by
    have h := sum_range_pow p (p - 1)
    rw [← Nat.cast_add_one, hsucc] at h
    rw [h, mul_sum]
    exact sum_congr rfl fun j _ => by
      rw [mul_comm (p : ℚ), div_mul_cancel₀ _ hpQ]
  have ht : t (p - 1) = (p : ℚ) ^ 2 * bernoulli (p - 1) := by
    have hsub : p - (p - 1) = 1 := by omega
    simp only [t, ← Nat.choose_symm (by omega : p - 1 ≤ p), hsub, Nat.choose_one_right, pow_one]
    ring
  have htail : ∑ j ∈ range (p - 1), t j =
      (p : ℚ) ^ 3 * ∑ j ∈ range (p - 1), bernoulli j * c j := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.mp hj
    have hcast : (p : ℚ) * c j = (p.choose j : ℚ) * (p : ℚ) ^ (p - j - 2) := by
      exact_mod_cast hc j hj'
    dsimp only [t]
    rw [show p - j = 2 + (p - j - 2) by omega, pow_add]
    linear_combination -(bernoulli j * (p : ℚ) ^ 2) * hcast
  have hsplit := sum_range_succ t (p - 1)
  rw [hsucc, htail, ht] at hsplit
  rw [hsplit] at hF
  let r : ℚ := ∑ j ∈ range (p - 1), bernoulli j * c j
  have herror : (Nat.factorial (p - 1) : ℚ) - (p * bernoulli (p - 1) - p) =
      (p : ℚ) ^ 2 * ((w : ℚ) + r) := by
    apply (mul_left_cancel₀ hpQ)
    linear_combination (p : ℚ) * hW + hF
  have hr : Rat.padicValuation p r ≤ 1 := by
    apply (Rat.padicValuation p).map_sum_le
    intro j hj
    rw [map_mul, bernoulli.eq_def, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul,
      Rat.padicValuation_natCast]
    exact mul_le_one' (MetaMathlibExt.padicValuation_bernoulli'_le_one j (by
      have := mem_range.mp hj
      omega)) (Int.padicValuation_le_one p _)
  have hwval : Rat.padicValuation p (w : ℚ) ≤ 1 := by
    rw [Rat.padicValuation_cast]
    exact Int.padicValuation_le_one p w
  have hval := (Rat.padicValuation p).map_add_le hwval hr
  have hnorm := Padic.norm_rat_le_one (p := p) (Rat.padicValuation_le_one_iff.mp hval)
  rw [Padic.eq_padicNorm] at hnorm
  have hbound : padicNorm p ((w : ℚ) + r) ≤ 1 := by exact_mod_cast hnorm
  rw [herror, padicNorm.mul]
  calc
    _ ≤ padicNorm p ((p : ℚ) ^ 2) * 1 := mul_le_mul_of_nonneg_left hbound (padicNorm.nonneg _)
    _ = (p : ℚ) ^ (-2 : ℤ) := by simp [pow_two, zpow_neg]

end MathlibExt.NumberTheory.WilsonFaulhaberWanted
