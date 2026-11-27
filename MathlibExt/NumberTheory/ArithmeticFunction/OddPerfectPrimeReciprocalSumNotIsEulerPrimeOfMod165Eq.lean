/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.EulerPrime
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Primes congruent to `-1` modulo `165` are not Euler primes

This module proves that no natural number `q` with `q % 165 = 164` is an Euler prime
of any natural number.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 9.
-/

namespace MetaMathlibExt

private theorem s9 : ∑ d ∈ Nat.divisors (3 ^ 2), d = 13 := by
  rw [← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
  norm_num [Finset.sum_range_succ]
private theorem s5 : ∑ d ∈ Nat.divisors 5, d = 6 := by
  have h : (5 : ℕ) = 5 ^ 1 := by norm_num
  rw [h, ← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 5)]
  norm_num [Finset.sum_range_succ]
private theorem s121 : ∑ d ∈ Nat.divisors (11 ^ 2), d = 133 := by
  rw [← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 11)]
  norm_num [Finset.sum_range_succ]
private theorem s13 : ∑ d ∈ Nat.divisors 13, d = 14 := by
  have h : (13 : ℕ) = 13 ^ 1 := by norm_num
  rw [h, ← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 13)]
  norm_num [Finset.sum_range_succ]
private theorem s81 : ∑ d ∈ Nat.divisors (3 ^ 4), d = 121 := by
  rw [← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
  norm_num [Finset.sum_range_succ]
private theorem s25 : ∑ d ∈ Nat.divisors (5 ^ 2), d = 31 := by
  rw [← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 5)]
  norm_num [Finset.sum_range_succ]
private theorem abundant_m0 :
    2 * (3 ^ 2 * 5 * 11 ^ 2 * 13) < ∑ d ∈ Nat.divisors (3 ^ 2 * 5 * 11 ^ 2 * 13), d := by
  have c1 : Nat.Coprime (3 ^ 2) 5 := by decide
  have c2 : Nat.Coprime (3 ^ 2 * 5) (11 ^ 2) := by decide
  have c3 : Nat.Coprime (3 ^ 2 * 5 * 11 ^ 2) 13 := by decide
  rw [show (3 : ℕ) ^ 2 * 5 * 11 ^ 2 * 13 = (3 ^ 2 * 5 * 11 ^ 2) * 13 from by ring]
  rw [c3.sum_divisors_mul, s13]
  rw [show (3 : ℕ) ^ 2 * 5 * 11 ^ 2 = (3 ^ 2 * 5) * 11 ^ 2 from by ring]
  rw [c2.sum_divisors_mul, s121]
  rw [show (3 : ℕ) ^ 2 * 5 = (3 ^ 2) * 5 from by ring]
  rw [c1.sum_divisors_mul, s9, s5]
  norm_num
private theorem abundant_m1 :
    2 * (3 ^ 4 * 5 ^ 2 * 11 ^ 2) < ∑ d ∈ Nat.divisors (3 ^ 4 * 5 ^ 2 * 11 ^ 2), d := by
  have c1 : Nat.Coprime (3 ^ 4) (5 ^ 2) := by decide
  have c2 : Nat.Coprime (3 ^ 4 * 5 ^ 2) (11 ^ 2) := by decide
  rw [show (3 : ℕ) ^ 4 * 5 ^ 2 * 11 ^ 2 = (3 ^ 4 * 5 ^ 2) * 11 ^ 2 from by ring]
  rw [c2.sum_divisors_mul, s121]
  rw [show (3 : ℕ) ^ 4 * 5 ^ 2 = (3 ^ 4) * 5 ^ 2 from by ring]
  rw [c1.sum_divisors_mul, s81, s25]
  norm_num
private theorem mul_sum_divisors_le_sum_divisors_of_dvd {m n t : ℕ} (hm : 0 < m) (ht : 0 < t)
    (h : n = m * t) : t * (∑ d ∈ Nat.divisors m, d) ≤ ∑ d ∈ Nat.divisors n, d := by
  have hn : 0 < n := by rw [h]; exact Nat.mul_pos hm ht
  have hn0 : n ≠ 0 := by omega
  have hdiv : ∀ d ∈ Nat.divisors m, d * t ∈ Nat.divisors n := by
    intro d hd
    rw [Nat.mem_divisors] at hd ⊢
    obtain ⟨hdvd, hm0⟩ := hd
    refine ⟨?_, hn0⟩
    obtain ⟨k, hk⟩ := hdvd
    use k
    rw [h, hk]
    ring
  have hinj : Set.InjOn (fun d => d * t) (Nat.divisors m : Set ℕ) := by
    intro d1 hd1 d2 hd2 heq
    simp only at heq
    exact Nat.mul_right_cancel ht heq
  have himg : Finset.image (fun d => d * t) (Nat.divisors m) ⊆ Nat.divisors n := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    exact hdiv d hd
  have hle := Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => Nat.zero_le i)
  rw [Finset.sum_image hinj] at hle
  have hmul : (∑ d ∈ Nat.divisors m, d) * t = ∑ d ∈ Nat.divisors m, d * t := by
    rw [Finset.sum_mul]
  calc t * (∑ d ∈ Nat.divisors m, d)
      = (∑ d ∈ Nat.divisors m, d) * t := mul_comm _ _
    _ = ∑ d ∈ Nat.divisors m, d * t := hmul
    _ ≤ ∑ d ∈ Nat.divisors n, d := hle
private theorem not_perfect_of_abundant_dvd {m n : ℕ} (hm : 0 < m)
    (hab : 2 * m < ∑ d ∈ Nat.divisors m, d) (hdvd : m ∣ n) : ¬ n.Perfect := by
  intro hper
  obtain ⟨t, ht⟩ := hdvd
  by_cases ht0 : t = 0
  · have hn0 : n = 0 := by rw [ht, ht0, mul_zero]
    rw [hn0] at hper
    have hpos : (0 : ℕ) < 0 := hper.2
    omega
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht0
    have hn : 0 < n := hper.2
    have hsum : ∑ d ∈ Nat.divisors n, d = 2 * n :=
      (Nat.perfect_iff_sum_divisors_eq_two_mul hn).mp hper
    have hle := mul_sum_divisors_le_sum_divisors_of_dvd hm htpos ht
    have hlt : t * (2 * m) < t * (∑ d ∈ Nat.divisors m, d) :=
      (Nat.mul_lt_mul_left htpos).mpr hab
    have heq : t * (2 * m) = 2 * n := by rw [ht]; ring
    omega
private theorem even_factorization_of_ne {N Q K M p : ℕ} (hEq : N = Q ^ K * M ^ 2)
    (hQprime : Q.Prime) (hCop : Q.Coprime M) (hNpos : 0 < N)
    (hp : p.Prime) (hne : p ≠ Q) : Even (N.factorization p) := by
  have hQ0 : Q ≠ 0 := hQprime.ne_zero
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [hEq] at hNpos
    simp at hNpos
  have hQK0 : Q ^ K ≠ 0 := pow_ne_zero _ hQ0
  have hM20 : M ^ 2 ≠ 0 := pow_ne_zero _ hM0
  have hfact : N.factorization p = (Q ^ K).factorization p + (M ^ 2).factorization p := by
    rw [hEq, Nat.factorization_mul hQK0 hM20, Finsupp.add_apply]
  have hQnot : ¬ p ∣ Q := by
    intro hdvd
    rw [Nat.dvd_prime hQprime] at hdvd
    rcases hdvd with h1 | hQ
    · exact hp.ne_one h1
    · exact hne hQ
  have hQfp : Q.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hQnot
  have hQKfp : (Q ^ K).factorization p = 0 := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, hQfp, smul_eq_mul, mul_zero]
  have hM2fp : (M ^ 2).factorization p = 2 * M.factorization p := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  rw [hfact, hQKfp, hM2fp, zero_add]
  exact ⟨M.factorization p, two_mul _⟩
private theorem sum_divisors_prime_pow_dvd_of_factorization {n p a : ℕ} (hp : p.Prime)
    (hn0 : n ≠ 0) (hfa : n.factorization p = a) :
    ∑ d ∈ Nat.divisors (p ^ a), d ∣ ∑ d ∈ Nat.divisors n, d := by
  have hpow_dvd : p ^ a ∣ n := by
    have h := Nat.ordProj_dvd n p
    rw [hfa] at h
    exact h
  obtain ⟨t, ht⟩ := hpow_dvd
  have hpa0 : p ^ a ≠ 0 := pow_ne_zero _ hp.ne_zero
  have ht0 : t ≠ 0 := by
    intro h0
    subst h0
    simp at ht
    exact hn0 ht
  have hpt : ¬ p ∣ t := by
    intro hdvd
    have hpos : 0 < t.factorization p := hp.factorization_pos_of_dvd ht0 hdvd
    have hfact : n.factorization p = (p ^ a).factorization p + t.factorization p := by
      rw [ht, Nat.factorization_mul hpa0 ht0, Finsupp.add_apply]
    rw [Nat.factorization_pow_self hp] at hfact
    omega
  have hcop : (p ^ a).Coprime t := (hp.coprime_iff_not_dvd.mpr hpt).pow_left a
  have hmul :
      ∑ d ∈ Nat.divisors n, d = (∑ d ∈ Nat.divisors (p ^ a), d) * ∑ d ∈ Nat.divisors t, d := by
    rw [ht]
    exact hcop.sum_divisors_mul
  rw [hmul]
  exact dvd_mul_right _ _
private theorem odd_of_mod4_eq_one {K : ℕ} (h : K % 4 = 1) : Odd K := Nat.odd_iff.mpr (by omega)
private theorem factorization_five_eq_one_of_components {n : ℕ} (hperf : n.Perfect)
    (h165 : 165 ∣ n) {Q S M : ℕ} (hQprime : Q.Prime) (hEq : n = Q ^ S * M ^ 2)
    (hQ4 : Q % 4 = 1) (hCop : Q.Coprime M) : n.factorization 5 = 1 := by
  have hn0 : n ≠ 0 := hperf.2.ne'
  have hnpos : 0 < n := hperf.2
  have h3prime : Nat.Prime 3 := by decide
  have h5prime : Nat.Prime 5 := by decide
  have h11prime : Nat.Prime 11 := by decide
  have h13prime : Nat.Prime 13 := by decide
  have hQ3 : Q ≠ 3 := by omega
  have hQ11 : Q ≠ 11 := by omega
  have h3n : 3 ∣ n := dvd_trans (by decide : (3 : ℕ) ∣ 165) h165
  have h5n : 5 ∣ n := dvd_trans (by decide : (5 : ℕ) ∣ 165) h165
  have h11n : 11 ∣ n := dvd_trans (by decide : (11 : ℕ) ∣ 165) h165
  have heven3 : Even (n.factorization 3) :=
    even_factorization_of_ne hEq hQprime hCop hnpos h3prime hQ3.symm
  have heven11 : Even (n.factorization 11) :=
    even_factorization_of_ne hEq hQprime hCop hnpos h11prime hQ11.symm
  have hpos3 : 0 < n.factorization 3 := h3prime.factorization_pos_of_dvd hn0 h3n
  have hpos11 : 0 < n.factorization 11 := h11prime.factorization_pos_of_dvd hn0 h11n
  have hge3 : 2 ≤ n.factorization 3 := by
    obtain ⟨k, hk⟩ := heven3
    omega
  have hge11 : 2 ≤ n.factorization 11 := by
    obtain ⟨k, hk⟩ := heven11
    omega
  have h9n : 3 ^ 2 ∣ n := (h3prime.pow_dvd_iff_le_factorization hn0).mpr hge3
  have h121n : 11 ^ 2 ∣ n := (h11prime.pow_dvd_iff_le_factorization hn0).mpr hge11
  have hne2 : n.factorization 3 ≠ 2 := by
    intro h2
    have hsig9_dvd : ∑ d ∈ Nat.divisors (3 ^ 2), d ∣ ∑ d ∈ Nat.divisors n, d :=
      sum_divisors_prime_pow_dvd_of_factorization h3prime hn0 h2
    rw [s9] at hsig9_dvd
    have hsigN : ∑ d ∈ Nat.divisors n, d = 2 * n :=
      (Nat.perfect_iff_sum_divisors_eq_two_mul hnpos).mp hperf
    rw [hsigN] at hsig9_dvd
    have h13n : 13 ∣ n :=
      Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 13 2) hsig9_dvd
    have hm0_dvd : 3 ^ 2 * 5 * 11 ^ 2 * 13 ∣ n := by
      have h45 : 3 ^ 2 * 5 ∣ n :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime (3 ^ 2) 5) h9n h5n
      have h45121 : 3 ^ 2 * 5 * 11 ^ 2 ∣ n :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime (3 ^ 2 * 5) (11 ^ 2)) h45 h121n
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
        (by decide : Nat.Coprime (3 ^ 2 * 5 * 11 ^ 2) 13) h45121 h13n
    exact not_perfect_of_abundant_dvd (by decide) abundant_m0 hm0_dvd hperf
  have hge4 : 4 ≤ n.factorization 3 := by
    obtain ⟨k, hk⟩ := heven3
    omega
  have h81n : 3 ^ 4 ∣ n := (h3prime.pow_dvd_iff_le_factorization hn0).mpr hge4
  have hfact5_lt2 : n.factorization 5 < 2 := by
    by_contra hcon
    have hcon2 : 2 ≤ n.factorization 5 := not_lt.mp hcon
    have h25n : 5 ^ 2 ∣ n := (h5prime.pow_dvd_iff_le_factorization hn0).mpr hcon2
    have hm1_dvd : 3 ^ 4 * 5 ^ 2 * 11 ^ 2 ∣ n := by
      have h81_25 : 3 ^ 4 * 5 ^ 2 ∣ n :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime (3 ^ 4) (5 ^ 2)) h81n h25n
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
        (by decide : Nat.Coprime (3 ^ 4 * 5 ^ 2) (11 ^ 2)) h81_25 h121n
    exact not_perfect_of_abundant_dvd (by decide) abundant_m1 hm1_dvd hperf
  have hpos5 : 0 < n.factorization 5 := h5prime.factorization_pos_of_dvd hn0 h5n
  omega
private theorem add_one_dvd_geom_sum_of_odd {Q K : ℕ} (hK : Odd K) :
    Q + 1 ∣ ∑ i ∈ Finset.range (K + 1), Q ^ i := by
  obtain ⟨t, ht⟩ := hK
  have hall : ∀ t : ℕ, Q + 1 ∣ ∑ i ∈ Finset.range (2 * t + 2), Q ^ i := by
    intro t
    induction t with
    | zero =>
      show Q + 1 ∣ ∑ i ∈ Finset.range 2, Q ^ i
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add,
        add_comm (1 : ℕ) Q]
      exact dvd_refl _
    | succ t ih =>
      have h1 : 2 * (t + 1) + 2 = (2 * t + 2) + 2 := by ring
      rw [h1]
      rw [show (2 * t + 2) + 2 = ((2 * t + 2) + 1) + 1 from by ring]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hpair : Q ^ (2 * t + 2) + Q ^ ((2 * t + 2) + 1) = Q ^ (2 * t + 2) * (Q + 1) := by
        rw [pow_succ]
        ring
      rw [add_assoc, hpair]
      exact Nat.dvd_add ih (dvd_mul_left _ _)
  have hK1 : K + 1 = 2 * t + 2 := by omega
  rw [hK1]
  exact hall t
private theorem dvd_165_of_eulerian {N Q K M : ℕ} (hEq : N = Q ^ K * M ^ 2)
    (hQprime : Q.Prime) (hCop : Q.Coprime M) (hPerf : N.Perfect) (hKodd : Odd K)
    (hq165 : Q % 165 = 164) : 165 ∣ N := by
  have hNpos : 0 < N := hPerf.2
  have hCop2 : (Q ^ K).Coprime (M ^ 2) := (hCop.pow_left K).pow_right 2
  have hsig_mul :
      ∑ d ∈ Nat.divisors N, d =
        (∑ d ∈ Nat.divisors (Q ^ K), d) * ∑ d ∈ Nat.divisors (M ^ 2), d := by
    rw [hEq]
    exact hCop2.sum_divisors_mul
  have hsig_N : ∑ d ∈ Nat.divisors N, d = 2 * N :=
    (Nat.perfect_iff_sum_divisors_eq_two_mul hNpos).mp hPerf
  have hsig_Q_dvd : ∑ d ∈ Nat.divisors (Q ^ K), d ∣ 2 * N := by
    have heq2 : 2 * N = (∑ d ∈ Nat.divisors (Q ^ K), d) * ∑ d ∈ Nat.divisors (M ^ 2), d :=
      hsig_N.symm.trans hsig_mul
    rw [heq2]
    exact dvd_mul_right _ _
  have hQ1_dvd_sig : Q + 1 ∣ ∑ d ∈ Nat.divisors (Q ^ K), d := by
    rw [← ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply_prime_pow hQprime]
    exact add_one_dvd_geom_sum_of_odd hKodd
  have h165_dvd_Q1 : 165 ∣ Q + 1 := by omega
  have h165_dvd_2N : 165 ∣ 2 * N := dvd_trans h165_dvd_Q1 (dvd_trans hQ1_dvd_sig hsig_Q_dvd)
  exact Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 165 2) h165_dvd_2N
private theorem main_of_components {n q : ℕ} (hq165 : q % 165 = 164)
    {K M : ℕ} (hPerf : n.Perfect) (hPrime : q.Prime)
    (hEq : n = q ^ K * M ^ 2) (hq4 : q % 4 = 1) (hk4 : K % 4 = 1)
    (hCop : q.Coprime M) : False := by
  have hKodd : Odd K := odd_of_mod4_eq_one hk4
  have h165n : 165 ∣ n := dvd_165_of_eulerian hEq hPrime hCop hPerf hKodd hq165
  have hfact5 : n.factorization 5 = 1 :=
    factorization_five_eq_one_of_components hPerf h165n hPrime hEq hq4 hCop
  have hq5 : q ≠ 5 := by omega
  have h5prime : Nat.Prime 5 := by decide
  have heven5 : Even (n.factorization 5) :=
    even_factorization_of_ne hEq hPrime hCop hPerf.2 h5prime hq5.symm
  rw [hfact5] at heven5
  obtain ⟨k, hk⟩ := heven5
  omega

/-- **Primes congruent to $-1$ modulo $165$ are not Euler primes.** For all natural numbers
$q$ and $N$ with $q \equiv -1 \pmod{165}$, $q$ is not an Euler prime of $N$. In particular, no
prime $q \equiv -1 \pmod{165}$ is the Euler prime of an odd perfect number.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 9 (`integers-2025-A59-prop-9`). -/
public theorem not_isEulerPrime_of_mod_165_eq
    (n q : ℕ) (hq : q % 165 = 164) :
    ¬ IsEulerPrime n q := by
  intro h
  obtain ⟨K, M, hE⟩ := h
  exact main_of_components hq (EulerianForm_perfect hE) (EulerianForm_prime hE)
    (EulerianForm_eq hE) (EulerianForm_mod4_q hE) (EulerianForm_mod4_k hE)
    (EulerianForm_coprime hE)

end MetaMathlibExt
