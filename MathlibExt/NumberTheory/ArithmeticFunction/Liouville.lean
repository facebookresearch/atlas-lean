/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Liouville
public import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

/-!
# Divisor sums and the Dirichlet series of the Liouville function

This file develops basic facts about Mathlib's Liouville function `ArithmeticFunction.liouville`,
`λ(n) = (-1) ^ Ω(n)`.

## Main statements

* `ArithmeticFunction.liouville_apply_prime_pow`: `λ(p ^ k) = (-1) ^ k`.
* `ArithmeticFunction.sum_divisors_liouville`: `∑_{d ∣ n} λ(d)` is `1` if `n` is a square and
  `0` otherwise.
* `LSeries_isSquare_indicator`: the Dirichlet series of the indicator function of the squares is
  `ζ(2s)`.
* `ArithmeticFunction.riemannZeta_mul_LSeries_liouville`: `ζ(s) L(λ, s) = ζ(2s)` for `1 < re s`.
* `ArithmeticFunction.LSeries_liouville_eq_riemannZeta_two_mul_div`: `L(λ, s) = ζ(2s) / ζ(s)`
  for `1 < re s`.
-/

@[expose] public section

open scoped ArithmeticFunction.zeta

namespace ArithmeticFunction

/-- The Liouville function at a prime power: `λ(p ^ k) = (-1) ^ k`. -/
theorem liouville_apply_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    liouville (p ^ k) = (-1) ^ k := by
  rw [liouville_apply (pow_ne_zero k hp.ne_zero), cardFactors_apply_prime_pow hp]

/-- The Liouville function takes the values `±1` at nonzero arguments. -/
theorem abs_liouville {n : ℕ} (hn : n ≠ 0) : |liouville n| = 1 := by
  simp [liouville_apply hn, abs_pow]

/-- The Liouville function is bounded by `1` in absolute value. -/
theorem abs_liouville_le_one (n : ℕ) : |liouville n| ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · exact (abs_liouville hn).le

private theorem liouville_mul_zeta_apply_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (liouville * (ζ : ArithmeticFunction ℤ)) (p ^ k) = if Even k then 1 else 0 := by
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  simp_rw [liouville_apply_prime_pow hp]
  rw [neg_one_geom_sum]
  by_cases hk : Even k <;> simp [hk, Nat.even_add_one]

/-- The divisor sum of the Liouville function is the indicator function of the squares:
`∑_{d ∣ n} λ(d) = 1` if `n` is a square and `0` otherwise, for `n ≠ 0`. -/
theorem sum_divisors_liouville {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, liouville d = if IsSquare n then 1 else 0 := by
  classical
  have hmul : (liouville * (ζ : ArithmeticFunction ℤ)).IsMultiplicative :=
    isMultiplicative_liouville.mul isMultiplicative_zeta.natCast
  rw [← coe_mul_zeta_apply, hmul.multiplicative_factorization _ hn, Finsupp.prod]
  rw [Finset.prod_congr rfl fun p hp => liouville_mul_zeta_apply_prime_pow
    (Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)) _, Finset.prod_boole]
  congr 1
  refine propext ⟨fun h => ?_, fun h p hp => ?_⟩
  · refine Nat.isSquare_iff_even_factorization.mpr fun p _ => ?_
    by_cases hp : p ∈ n.factorization.support
    · exact h p hp
    · rw [Finsupp.notMem_support_iff.mp hp]
      exact Even.zero
  · rw [Nat.support_factorization] at hp
    exact Nat.isSquare_iff_even_factorization.mp h p (Nat.prime_of_mem_primeFactors hp)

/-- The Liouville Dirichlet series converges absolutely on `1 < re s`. -/
theorem LSeriesSummable_liouville {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (liouville n : ℂ)) s := by
  refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ ↦ ?_) hs
  rw [Complex.norm_intCast]
  exact_mod_cast abs_liouville_le_one n

end ArithmeticFunction

/-- The Dirichlet series of the indicator function of the squares is `ζ(2s)`. -/
theorem LSeries_isSquare_indicator {s : ℂ} (hs : 1 / 2 < s.re) :
    LSeries (fun n ↦ if IsSquare n then 1 else 0) s = riemannZeta (2 * s) := by
  classical
  have hs2 : 1 < (2 * s).re := by simp; linarith
  rw [← LSeries_one_eq_riemannZeta hs2]
  simp only [LSeries]
  rw [← (Nat.pow_left_injective (n := 2) two_ne_zero).tsum_eq]
  · refine tsum_congr fun m => ?_
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rw [LSeries.term_of_ne_zero (pow_ne_zero 2 hm), LSeries.term_of_ne_zero hm,
      ite_eq_left ⟨m, sq m⟩, Pi.one_apply, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
    norm_num
  · intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · exact ⟨0, rfl⟩
    by_cases hsq : IsSquare n
    · obtain ⟨r, rfl⟩ := hsq
      exact ⟨r, sq r⟩
    · simp [LSeries.term_of_ne_zero hn0, hsq] at hn

namespace ArithmeticFunction

/-- The Liouville Dirichlet series satisfies `ζ(s) L(λ, s) = ζ(2s)` for `1 < re s`. -/
theorem riemannZeta_mul_LSeries_liouville {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * LSeries (fun n ↦ (liouville n : ℂ)) s = riemannZeta (2 * s) := by
  classical
  have hconv : ∀ {n : ℕ}, n ≠ 0 → LSeries.convolution (fun n ↦ (liouville n : ℂ)) 1 n =
      if IsSquare n then 1 else 0 := by
    intro n hn
    rw [LSeries.convolution_def]
    simp only [Pi.one_apply, mul_one]
    rw [Nat.sum_divisorsAntidiagonal (fun x _ ↦ (liouville x : ℂ)), ← Int.cast_sum,
      sum_divisors_liouville hn]
    split_ifs <;> simp
  rw [← LSeries_isSquare_indicator (by linarith), ← LSeries_congr hconv,
    LSeries_convolution' (LSeriesSummable_liouville hs) (LSeriesSummable_one_iff.mpr hs),
    LSeries_one_eq_riemannZeta hs, mul_comm]

/-- The Dirichlet series of the Liouville function is `ζ(2s) / ζ(s)` for `1 < re s`. -/
theorem LSeries_liouville_eq_riemannZeta_two_mul_div {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ (liouville n : ℂ)) s = riemannZeta (2 * s) / riemannZeta s := by
  rw [eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs), mul_comm,
    riemannZeta_mul_LSeries_liouville hs]

end ArithmeticFunction
