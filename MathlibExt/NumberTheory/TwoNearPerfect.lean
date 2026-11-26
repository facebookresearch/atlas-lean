/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Two-near perfect numbers of the forms `2 ^ k * p` and `2 ^ k * p ^ 2`

Results from Aryan, Madhavani, Parikh, Slattery and Zelinsky, *On 2-Near Perfect Numbers*:

* `strong_two_near_perfect_two_pow_mul_prime_form`: the prime in a strongly `2`-near perfect
  number `2 ^ k * p` satisfies `p * (1 + 2 ^ (k - a)) = 2 ^ (k + 1) - 2 ^ a - 1` for some `a ≤ k`
  (Lemma 8).
* `not_two_near_perfect_two_pow_mul_prime_sq_case_two`: no `2 ^ k * p ^ 2` is `2`-near perfect
  with omitted divisors `2 ^ i` and `p` or `p ^ 2` (Proposition 2).
* `eq_one_of_isSquare_discriminant`: if `1 ≤ a ≤ k` and
  `2 ^ (2 * k + 2) + 2 ^ (k + 2) - 2 ^ (a + 2) - 7` is the square of an integer, then
  `k = a = 1` (Lemma 2).
-/

namespace MetaMathlibExt

open ArithmeticFunction

private theorem divisor_form {k p d : ℕ} (hp : p.Prime)
    (hdvd : d ∣ 2 ^ k * p) : ∃ a ≤ k, d = 2 ^ a ∨ d = 2 ^ a * p := by
  by_cases hpd : p ∣ d
  · obtain ⟨t, rfl⟩ := hpd
    have ht : t ∣ 2 ^ k := by
      have h := hdvd
      rw [mul_comm (2 ^ k) p] at h
      exact (Nat.mul_dvd_mul_iff_left hp.pos).mp h
    obtain ⟨a, ha, h0⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ht
    exact ⟨a, ha, Or.inr (by rw [h0]; ring)⟩
  · have hcop : d.Coprime p := ((hp.coprime_iff_not_dvd).mpr hpd).symm
    have hd2 : d ∣ 2 ^ k := hcop.dvd_of_dvd_mul_right hdvd
    obtain ⟨a, ha, h0⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
    exact ⟨a, ha, Or.inl h0⟩

private theorem div_pow {k p a : ℕ} (ha : a ≤ k) :
    2 ^ k * p / 2 ^ a = 2 ^ (k - a) * p := by
  have hpow : 2 ^ k = 2 ^ a * 2 ^ (k - a) := by
    rw [← pow_add, Nat.add_sub_cancel' ha]
  apply Nat.div_eq_of_eq_mul_left (Nat.two_pow_pos a)
  rw [hpow]
  ring

private theorem div_pow_mul {k p a : ℕ} (hp : p.Prime) (ha : a ≤ k) :
    2 ^ k * p / (2 ^ a * p) = 2 ^ (k - a) := by
  have hpow : 2 ^ k = 2 ^ a * 2 ^ (k - a) := by
    rw [← pow_add, Nat.add_sub_cancel' ha]
  have hpos : 0 < 2 ^ a * p := Nat.mul_pos (Nat.two_pow_pos a) hp.pos
  apply Nat.div_eq_of_eq_mul_left hpos
  rw [hpow]
  ring

private theorem form_of_sigma_eq {k p a : ℕ}
    (htwo : sigma 1 (2 ^ k) + 1 = 2 * 2 ^ k)
    (hσ : sigma 1 (2 ^ k) * (1 + p) = 2 * (2 ^ k * p) + 2 ^ a + 2 ^ (k - a) * p) :
    (p : ℤ) * (1 + 2 ^ (k - a)) = 2 ^ (k + 1) - 2 ^ a - 1 := by
  have hσz : (sigma 1 (2 ^ k) : ℤ) * (1 + (p : ℤ)) =
      2 * ((2 : ℤ) ^ k * p) + 2 ^ a + 2 ^ (k - a) * p := by
    exact_mod_cast hσ
  have htwoz : (sigma 1 (2 ^ k) : ℤ) + 1 = 2 * (2 : ℤ) ^ k := by
    exact_mod_cast htwo
  rw [pow_succ']
  linear_combination (1 + (p : ℤ)) * htwoz - hσz

/-- **Strongly $2$-near perfect numbers of the form $2^k p$.** Let $p$ be an odd prime, let $k$
be a natural number and let $n = 2^k p$. Suppose that $n$ is strongly $2$-near perfect, that is,
$\sigma(n) = 2n + d + n/d$ for some divisor $d$ of $n$, where $\sigma$ is the sum-of-divisors
function. Then there is a natural number $a \le k$ with $p(1 + 2^{k-a}) = 2^{k+1} - 2^a - 1$,
that is, $p = (2^{k+1} - 2^a - 1)/(1 + 2^{k-a})$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 8
(`integers-2024-A61-lem-8`). -/
public theorem strong_two_near_perfect_two_pow_mul_prime_form {k p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hstrong : ∃ d, d ∣ 2 ^ k * p ∧
      ArithmeticFunction.sigma 1 (2 ^ k * p) = 2 * (2 ^ k * p) + d + 2 ^ k * p / d) :
    ∃ a ≤ k, (p : ℤ) * (1 + 2 ^ (k - a)) = 2 ^ (k + 1) - 2 ^ a - 1 := by
  obtain ⟨d, hdvd, hσ⟩ := hstrong
  have htwo : sigma 1 (2 ^ k) + 1 = 2 * 2 ^ k := by
    rw [sigma_one_apply_prime_pow Nat.prime_two]
    simpa only [one_add_one_eq_two, mul_one, pow_succ'] using geom_sum_mul_add (1 : ℕ) (k + 1)
  have hprime : sigma 1 p = 1 + p := by
    have h := sigma_one_apply_prime_pow (i := 1) hp
    rw [pow_one] at h
    simpa [Finset.sum_range_succ] using h
  have hcop : (2 ^ k).Coprime p :=
    ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).pow_left k
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, hprime] at hσ
  obtain ⟨a, ha, hd | hd⟩ := divisor_form hp hdvd
  · rw [hd, div_pow ha] at hσ
    exact ⟨a, ha, form_of_sigma_eq htwo hσ⟩
  · rw [hd, div_pow_mul hp ha] at hσ
    refine ⟨k - a, Nat.sub_le k a, ?_⟩
    have hsub : k - (k - a) = a := Nat.sub_sub_self ha
    have hσ' : sigma 1 (2 ^ k) * (1 + p) =
        2 * (2 ^ k * p) + 2 ^ (k - a) + 2 ^ (k - (k - a)) * p := by
      rw [hsub]
      linear_combination hσ
    simpa [hsub] using form_of_sigma_eq htwo hσ'

/-- **No $2$-near perfect $2^k p^2$ with omitted divisors $2^i$ and $p$ or $p^2$.** Let $p$ be an
odd prime, let $k$ and $i$ be natural numbers with $i \le k$, let $m$ be $1$ or $2$, and let
$n = 2^k p^2$. Then $\sigma(n) \ne 2n + 2^i + p^m$, where $\sigma$ is the sum-of-divisors
function; that is, $n$ is not $2$-near perfect with omitted divisors $2^i$ and $p^m$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Proposition 2
(`integers-2024-A61-prop-2`). -/
public theorem not_two_near_perfect_two_pow_mul_prime_sq_case_two {k p i m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hi : i ≤ k) (hm : m = 1 ∨ m = 2) :
    ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) ≠ 2 * (2 ^ k * p ^ 2) + 2 ^ i + p ^ m := by
  intro hσ
  have htwo : sigma 1 (2 ^ k) + 1 = 2 * 2 ^ k := by
    rw [sigma_one_apply_prime_pow Nat.prime_two]
    simpa only [one_add_one_eq_two, mul_one, pow_succ'] using geom_sum_mul_add (1 : ℕ) (k + 1)
  have hsquare : sigma 1 (p ^ 2) = 1 + p + p ^ 2 := by
    simp [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]
  rw [isMultiplicative_sigma.map_mul_of_coprime
    (Nat.coprime_pow_primes k 2 Nat.prime_two hp hp2.symm), hsquare] at hσ
  have heq : (p + 1) * (2 * 2 ^ k) = p ^ 2 + p + 1 + 2 ^ i + p ^ m := by
    nlinarith only [hσ, congrArg (fun t => t * (1 + p + p ^ 2)) htwo]
  have hpow : 2 ^ i ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hi
  have hpos : 0 < (2 : ℤ) ^ i := pow_pos (by decide) i
  have hpcast : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  zify at heq hpow
  rcases hm with rfl | rfl
  · simp only [pow_one] at heq
    have hfactor : ((p : ℤ) + 1) * (2 * 2 ^ k - p - 1) = 2 ^ i := by
      nlinarith only [heq]
    have hy : 1 ≤ (2 : ℤ) * 2 ^ k - p - 1 := by
      by_contra h
      have hmul := mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ (p : ℤ) + 1 by omega)
        (show (2 : ℤ) * 2 ^ k - p - 1 ≤ 0 by omega)
      nlinarith only [hfactor, hpos, hmul]
    have hmul := mul_nonneg (show 0 ≤ (p : ℤ) by omega)
      (show 0 ≤ (2 : ℤ) * 2 ^ k - p - 2 by omega)
    nlinarith only [hfactor, hpow, hmul, hy, hpcast]
  · have hfactor : ((p : ℤ) + 1) * (2 * 2 ^ k - 2 * p + 1) = 2 ^ i + 2 := by
      nlinarith only [heq]
    have hy : 1 ≤ (2 : ℤ) * 2 ^ k - 2 * p + 1 := by
      by_contra h
      have hmul := mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ (p : ℤ) + 1 by omega)
        (show (2 : ℤ) * 2 ^ k - 2 * p + 1 ≤ 0 by omega)
      nlinarith only [hfactor, hpos, hmul]
    have hy' : (2 : ℤ) * 2 ^ k - 2 * p + 1 ≤ 1 := by
      by_contra h
      have hmul := mul_nonneg (show 0 ≤ (p : ℤ) by omega)
        (show 0 ≤ (2 : ℤ) * 2 ^ k - 2 * p - 1 by omega)
      nlinarith only [hfactor, hpow, hmul, hpcast,
        show 2 ≤ (2 : ℤ) * 2 ^ k - 2 * p + 1 by omega]
    have hprime : 2 ^ k = p := by
      exact_mod_cast (show (2 : ℤ) ^ k = p by omega)
    exact hp2 (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two
      (by rw [hprime]))

-- No integer square lies strictly between `t ^ 2` and `(t + 1) ^ 2`.
private theorem not_isSquare_of_between_consec_sq {D t : ℤ} (ht : 0 ≤ t)
    (hlo : t ^ 2 < D) (hhi : D < (t + 1) ^ 2) : ¬ IsSquare D := by
  rintro ⟨r, rfl⟩
  have h1 : |t| < |r| := sq_lt_sq.mp (by simpa only [pow_two] using hlo)
  have h2 : |r| < t + 1 :=
    abs_lt_of_sq_lt_sq (by simpa only [pow_two] using hhi) (by omega)
  rw [abs_of_nonneg ht] at h1
  omega

/-- **Square values of the discriminant $2^{2k+2} + 2^{k+2} - 2^{a+2} - 7$.** Let $a$ and $k$ be
natural numbers with $1 \le a \le k$. If $2^{2k+2} + 2^{k+2} - 2^{a+2} - 7$ is the square of an
integer, then $k = a = 1$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 2
(`integers-2024-A61-lem-2`). -/
public theorem eq_one_of_isSquare_discriminant {a k : ℕ} (ha : 0 < a) (hak : a ≤ k)
    (hD : IsSquare ((2 : ℤ) ^ (2 * k + 2) + 2 ^ (k + 2) - 2 ^ (a + 2) - 7)) :
    k = 1 ∧ a = 1 := by
  have hsq : (2 : ℤ) ^ (2 * k + 2) = ((2 : ℤ) ^ (k + 1)) ^ 2 := by
    rw [show 2 * k + 2 = (k + 1) * 2 from by ring, pow_mul]
  have h2k : (2 : ℤ) ^ (k + 2) = 2 * (2 : ℤ) ^ (k + 1) := by
    rw [show k + 2 = (k + 1) + 1 from by ring, pow_succ]
    ring
  have h2pos : (0 : ℤ) < 2 ^ (a + 2) := pow_pos (show (0 : ℤ) < 2 from by norm_num) _
  rcases eq_or_lt_of_le hak with rfl | hlt
  · by_cases ha1 : a = 1
    · exact ⟨ha1, ha1⟩
    · have ha2 : 1 < a := by omega
      have h4 : (4 : ℤ) < 2 ^ (a + 1) := by
        have h := pow_lt_pow_right₀ (show (1 : ℤ) < 2 from one_lt_two)
          (show 2 < a + 1 from by omega)
        rwa [show (2 : ℤ) ^ 2 = 4 from by norm_num] at h
      have hexp : ((2 : ℤ) ^ (a + 1) - 1) ^ 2 =
          ((2 : ℤ) ^ (a + 1)) ^ 2 - 2 * 2 ^ (a + 1) + 1 := by ring
      have hlo : ((2 : ℤ) ^ (a + 1) - 1) ^ 2 <
          (2 : ℤ) ^ (2 * a + 2) + 2 ^ (a + 2) - 2 ^ (a + 2) - 7 := by
        rw [hsq, h2k, hexp]
        linarith
      have hhi : (2 : ℤ) ^ (2 * a + 2) + 2 ^ (a + 2) - 2 ^ (a + 2) - 7 <
          ((2 : ℤ) ^ (a + 1) - 1 + 1) ^ 2 := by
        rw [show ((2 : ℤ) ^ (a + 1) - 1 + 1) = (2 : ℤ) ^ (a + 1) from by ring, hsq, h2k]
        linarith
      have ht : (0 : ℤ) ≤ 2 ^ (a + 1) - 1 := by omega
      exact absurd hD (not_isSquare_of_between_consec_sq ht hlo hhi)
  · have hk2 : 1 < k := by omega
    have hak1 : a + 2 ≤ k + 1 := by omega
    have hpow : (2 : ℤ) ^ (a + 2) ≤ 2 ^ (k + 1) :=
      pow_le_pow_right₀ (show (1 : ℤ) ≤ 2 from by norm_num) hak1
    have hu8 : (8 : ℤ) ≤ 2 ^ (k + 1) := by
      have h := pow_le_pow_right₀ (show (1 : ℤ) ≤ 2 from by norm_num)
        (show 3 ≤ k + 1 from by omega)
      rwa [show (2 : ℤ) ^ 3 = 8 from by norm_num] at h
    have hexp : ((2 : ℤ) ^ (k + 1) + 1) ^ 2 =
        ((2 : ℤ) ^ (k + 1)) ^ 2 + 2 * 2 ^ (k + 1) + 1 := by ring
    have hlo : ((2 : ℤ) ^ (k + 1)) ^ 2 <
        (2 : ℤ) ^ (2 * k + 2) + 2 ^ (k + 2) - 2 ^ (a + 2) - 7 := by
      rw [hsq, h2k]
      linarith
    have hhi : (2 : ℤ) ^ (2 * k + 2) + 2 ^ (k + 2) - 2 ^ (a + 2) - 7 <
        ((2 : ℤ) ^ (k + 1) + 1) ^ 2 := by
      rw [hsq, h2k, hexp]
      linarith
    have ht : (0 : ℤ) ≤ 2 ^ (k + 1) := pow_nonneg (show (0 : ℤ) ≤ 2 from by norm_num) _
    exact absurd hD (not_isSquare_of_between_consec_sq ht hlo hhi)

end MetaMathlibExt
