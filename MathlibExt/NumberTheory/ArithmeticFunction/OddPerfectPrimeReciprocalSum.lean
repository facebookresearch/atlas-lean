/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficient
public import MathlibExt.NumberTheory.EulerPrime
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Rat.BigOperators
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.ArithmeticFunction.AbundancyIndexDiv
import MathlibExt.NumberTheory.ArithmeticFunction.AbundancySupDivIndex
import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeProduct

/-!
# Prime reciprocal sums of odd perfect and primitive non-deficient numbers

## Main statements

* `eulerianForm_exponent_eq_one_or_pow_five_lt`: if `(n, q, e, m)` is in Eulerian form then
  `e = 1` or `q ^ 5 < 2 * m ^ 2` (Proposition 11).
* `oddPerfect_abundancySup_le`: an upper bound on `H(n) = ∏_{p ∣ n} p/(p-1)` for an odd perfect
  number `n` in terms of its least prime factor `n.minFac` (Proposition 5).
* `exists_abundancySup_le_two_add_div_minFac`: there is a real constant `C` such that every
  primitive non-deficient number `n` with least prime factor `p₁` satisfies `H(n) ≤ 2 + C/p₁`,
  where `H(n)` is `abundancySup` (Proposition 8).
* `not_abundancySup_oddPart_succ_lt_two_and_two_lt`: there is no odd prime `q` with
  `H(odd(q+1)) < 2` and `H(q * odd(q+1)) > 2`, where `odd` is the largest odd divisor
  (Proposition 10, corrected to odd primes). The proof combines the prime bound
  `le_two_mul_prod_sub_one_sub_one_of_two_lt` with the factorization `q + 1 = 2 ^ a * m`.

## References

* Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd Perfect or Odd
  Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59 (arXiv:2402.14234v5),
  Propositions 5, 8, 10 (corrected to odd primes) and 11. The paper writes
  `H(n) = ∏_{p ∣ n} p/(p-1)` for `abundancySup` and `p₁` for `n.minFac`.
-/

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

namespace MetaMathlibExt

/-- **Fifth-power bound on the Euler prime of an odd perfect number.** If $(n, q, e, m)$ is in
Eulerian form, that is, $n$ is an odd perfect number, $q$ is a prime coprime to $m$,
$n = q^e m^2$ and $q \equiv e \equiv 1 \pmod 4$, then $e = 1$ or $q^5 < 2m^2$, that is,
$q < 2^{1/5} m^{2/5}$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 11 (`integers-2025-A59-prop-11`). -/
public theorem eulerianForm_exponent_eq_one_or_pow_five_lt
    (n q e m : ℕ) (h : EulerianForm n q e m) :
    e = 1 ∨ q ^ 5 < 2 * m ^ 2 := by
  obtain ⟨hperf, _hodd, hq, hnm, _hq4, he4, hcop⟩ := h
  by_cases he1 : e = 1
  · exact Or.inl he1
  · right
    have he5 : 5 ≤ e := by omega
    have hn_pos : 0 < n := hperf.2
    have hm_pos : 0 < m := by
      by_contra hcon
      have hm0 : m = 0 := by omega
      rw [hm0, zero_pow two_ne_zero, mul_zero] at hnm
      omega
    have hcop_pow : (q ^ e).Coprime (m ^ 2) := hcop.pow e 2
    have hsigma_mul : (ArithmeticFunction.sigma 1) (q ^ e * m ^ 2)
        = (ArithmeticFunction.sigma 1) (q ^ e) * (ArithmeticFunction.sigma 1) (m ^ 2) :=
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop_pow
    have hsigma_n : (ArithmeticFunction.sigma 1) (q ^ e)
        * (ArithmeticFunction.sigma 1) (m ^ 2) = 2 * (q ^ e * m ^ 2) := by
      rw [← hsigma_mul, ← hnm, ArithmeticFunction.sigma_one_apply]
      exact (Nat.perfect_iff_sum_divisors_eq_two_mul hn_pos).mp hperf
    have hS_sum : (ArithmeticFunction.sigma 1) (q ^ e)
        = ∑ k ∈ Finset.range (e + 1), q ^ k :=
      ArithmeticFunction.sigma_one_apply_prime_pow hq
    have hS_split : (ArithmeticFunction.sigma 1) (q ^ e)
        = 1 + q * (∑ k ∈ Finset.range e, q ^ k) := by
      rw [hS_sum, Finset.sum_range_succ']
      have hpow : ∀ k ∈ Finset.range e, q ^ (k + 1) = q * q ^ k :=
        fun k _ => pow_succ' q k
      rw [Finset.sum_congr rfl hpow, ← Finset.mul_sum, pow_zero, add_comm]
    have hS_cop : ((ArithmeticFunction.sigma 1) (q ^ e)).Coprime (q ^ e) := by
      have hq1 : Nat.Coprime q (1 + q * (∑ k ∈ Finset.range e, q ^ k)) :=
        (Nat.coprime_add_mul_left_right q 1 _).mpr (Nat.coprime_one_right q)
      have hSq : ((ArithmeticFunction.sigma 1) (q ^ e)).Coprime q := by
        rw [hS_split]
        exact hq1.symm
      simpa using hSq.pow 1 e
    have hS_dvd : (ArithmeticFunction.sigma 1) (q ^ e) ∣ q ^ e * (2 * m ^ 2) :=
      ⟨(ArithmeticFunction.sigma 1) (m ^ 2), by rw [hsigma_n]; ring⟩
    have hS_dvd2 : (ArithmeticFunction.sigma 1) (q ^ e) ∣ 2 * m ^ 2 :=
      hS_cop.dvd_of_dvd_mul_left hS_dvd
    have hS_le : (ArithmeticFunction.sigma 1) (q ^ e) ≤ 2 * m ^ 2 :=
      Nat.le_of_dvd (by have h2 : 0 < m ^ 2 := pow_pos hm_pos 2; omega) hS_dvd2
    have hSq_lt : q ^ e < (ArithmeticFunction.sigma 1) (q ^ e) := by
      rw [hS_sum, Finset.sum_range_succ]
      have hmem : 0 ∈ Finset.range e := Finset.mem_range.mpr (by omega)
      have h1 : 1 ≤ ∑ k ∈ Finset.range e, q ^ k := by
        have hle := Finset.single_le_sum (s := Finset.range e) (f := fun k => q ^ k)
          (fun i _ => Nat.zero_le _) hmem
        simpa using hle
      omega
    have hq5 : q ^ 5 ≤ q ^ e := Nat.pow_le_pow_right hq.pos he5
    calc q ^ 5 ≤ q ^ e := hq5
      _ < (ArithmeticFunction.sigma 1) (q ^ e) := hSq_lt
      _ ≤ 2 * m ^ 2 := hS_le

private theorem abundancyIndex_eq_two_of_perfect (n : ℕ) (hperf : n.Perfect) :
    abundancyIndex n = 2 := by
  have hpos : 0 < n := hperf.2
  have hsum := (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp hperf
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  simp only [abundancyIndex, hsum, Nat.cast_mul, Nat.cast_ofNat]
  exact mul_div_cancel_right₀ 2 hn0

private theorem minFac_ge_three (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) :
    3 ≤ n.minFac := by
  have hpos : 0 < n := hperf.2
  have hn1 : n ≠ 1 := by
    intro h
    have hsum := (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp hperf
    rw [h] at hsum
    simp at hsum
  have hp : n.minFac.Prime := Nat.minFac_prime hn1
  have h2 : n.minFac ≠ 2 := fun h => hodd.not_two_dvd_nat (h ▸ Nat.minFac_dvd n)
  have hle := hp.two_le
  omega

private theorem odd_of_mem_primeFactors (n p : ℕ) (hodd : Odd n)
    (hp : p ∈ n.primeFactors) : Odd p := by
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  rcases hprime.eq_two_or_odd with rfl | hmod
  · exact absurd hdvd hodd.not_two_dvd_nat
  · exact Nat.odd_iff.mpr hmod

private theorem sum_range_two_mul (f : ℕ → ℕ) (T : ℕ) :
    ∑ i ∈ Finset.range (2 * T), f i =
      ∑ i ∈ Finset.range T, (f (2 * i) + f (2 * i + 1)) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have h2 : 2 * (T + 1) = (2 * T + 1) + 1 := by ring
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

private theorem succ_dvd_sigma_prime_pow (q a : ℕ) (hq : q.Prime) (ha : Odd a) :
    q + 1 ∣ (ArithmeticFunction.sigma 1) (q ^ a) := by
  obtain ⟨t, ht⟩ := ha
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hq]
  have ha2 : a + 1 = 2 * (t + 1) := by omega
  rw [ha2, sum_range_two_mul]
  refine Finset.dvd_sum fun i _ => ?_
  have hfac : q ^ (2 * i) + q ^ (2 * i + 1) = (q + 1) * q ^ (2 * i) := by
    rw [pow_succ]
    ring
  exact ⟨q ^ (2 * i), hfac⟩

private theorem two_minFac_le_succ_of_euler (n q a r : ℕ) (hodd : Odd n)
    (hperf : n.Perfect) (hq : q.Prime) (hqmem : q ∈ n.primeFactors)
    (hn : n = q ^ a * r ^ 2) (ha : Odd a) (hcop : q.Coprime r) :
    2 * n.minFac ≤ q + 1 := by
  have hpos : 0 < n := hperf.2
  have hqodd : Odd q := odd_of_mem_primeFactors n q hodd hqmem
  have hσ2n : (ArithmeticFunction.sigma 1) n = 2 * n := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp hperf
  have hcop' : (q ^ a).Coprime (r ^ 2) := hcop.pow a 2
  have hmult : (ArithmeticFunction.sigma 1) (q ^ a * r ^ 2) =
      (ArithmeticFunction.sigma 1) (q ^ a) * (ArithmeticFunction.sigma 1) (r ^ 2) :=
    ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_sigma hcop'.gcd_eq_one
  rw [← hn] at hmult
  have hdvd1 : (ArithmeticFunction.sigma 1) (q ^ a) ∣ 2 * n := by
    rw [← hσ2n, hmult]
    exact ⟨_, rfl⟩
  have hdvd2 : q + 1 ∣ 2 * n :=
    (succ_dvd_sigma_prime_pow q a hq ha).trans hdvd1
  obtain ⟨t, ht⟩ := hqodd
  have h2 : 2 * (t + 1) ∣ 2 * n := by
    have hq1 : q + 1 = 2 * (t + 1) := by omega
    rw [← hq1]
    exact hdvd2
  have hdvd3 : t + 1 ∣ n := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp h2
  have ht2 : 2 ≤ t + 1 := by
    have hq3 : 3 ≤ q := by
      have h2le := hq.two_le
      have hne : q ≠ 2 := by
        intro h
        omega
      omega
    omega
  have hle : n.minFac ≤ t + 1 := Nat.minFac_le_of_dvd ht2 hdvd3
  have hq1 : q + 1 = 2 * (t + 1) := by omega
  omega

private theorem exists_single_odd_exponent (n : ℕ) (hodd : Odd n)
    (hperf : n.Perfect) :
    ∃ j, j ∈ n.primeFactors ∧ Odd (n.factorization j) ∧
      (∀ p ∈ n.primeFactors, p ≠ j → Even (n.factorization p)) ∧
      2 * n.minFac ≤ j + 1 := by
  obtain ⟨q, s, m, hqprime, hn_eq, hqmod, hsmod, hcop⟩ :=
    euler_odd_perfect_form n hodd hperf
  have hs4 : s % 4 = 1 := hsmod
  have hsodd : Odd s := ⟨2 * (s / 4), by
    have h4 := hs4
    clear hn_eq hqmod hcop hqprime hsmod hodd hperf
    omega⟩
  have hsne : s ≠ 0 := by
    have h4 := hs4
    clear hn_eq hqmod hcop hqprime hsmod hodd hperf hsodd
    omega
  have hn0 : n ≠ 0 := hperf.2.ne'
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hsne
  have hqdvd : q ∣ n := ⟨q ^ t * m ^ 2, by rw [hn_eq, pow_succ', mul_assoc]⟩
  have hqmem : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hqprime, hqdvd, hn0⟩
  have hq0 : q ≠ 0 := hqprime.pos.ne'
  have hm0 : m ≠ 0 := by
    intro h
    have hn0' : n = 0 := by simpa [h] using hn_eq
    exact hn0 hn0'
  have hpow1 : q ^ (t + 1) ≠ 0 := pow_ne_zero _ hq0
  have hpow2 : m ^ 2 ≠ 0 := pow_ne_zero _ hm0
  have hqnm : ¬ q ∣ m := hqprime.coprime_iff_not_dvd.mp hcop
  have hfact_q : n.factorization q = t + 1 := by
    have h1 : (q ^ (t + 1)).factorization q = t + 1 :=
      Nat.factorization_pow_self hqprime
    have hm0' : m.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hqnm
    have h2 : (m ^ 2).factorization q = 0 := by
      simp [Nat.factorization_pow, Finsupp.smul_apply, hm0']
    rw [hn_eq, Nat.factorization_mul hpow1 hpow2, Finsupp.add_apply, h1, h2,
      add_zero]
  have hqodd : Odd (n.factorization q) := by
    rw [hfact_q]
    exact hsodd
  have heven : ∀ p ∈ n.primeFactors, p ≠ q → Even (n.factorization p) := by
    intro p hpm hpq
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpm
    have hpdvd : ¬ p ∣ q ^ (t + 1) := by
      intro h
      have h2 : p ∣ q := hpprime.dvd_of_dvd_pow h
      have h3 : p = q := (Nat.prime_dvd_prime_iff_eq hpprime hqprime).mp h2
      exact hpq h3
    have h1 : (q ^ (t + 1)).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hpdvd
    have h2 : (m ^ 2).factorization p = 2 * (m.factorization p) := by
      simp [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    rw [hn_eq, Nat.factorization_mul hpow1 hpow2, Finsupp.add_apply, h1, h2,
      zero_add]
    exact ⟨m.factorization p, by omega⟩
  have h2m := two_minFac_le_succ_of_euler n q (t + 1) m hodd hperf hqprime hqmem
    hn_eq hsodd hcop
  exact ⟨q, hqmem, hqodd, heven, h2m⟩

private theorem one_div_cube_le (k : ℕ) (hk : 3 ≤ k) :
    1 / (k : ℚ) ^ 3 ≤ (1 / ((k : ℚ) - 2) ^ 2 - 1 / (k : ℚ) ^ 2) / 4 := by
  have hkR : (3 : ℚ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℚ) < k := by linarith
  have hk2 : (0 : ℚ) < (k : ℚ) - 2 := by linarith
  have hk0' : (k : ℚ) ≠ 0 := ne_of_gt hk0
  have hk2' : (k : ℚ) - 2 ≠ 0 := ne_of_gt hk2
  have hk2s' : ((k : ℚ) - 2) ^ 2 ≠ 0 := pow_ne_zero 2 hk2'
  have hks' : (k : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hk0'
  have e : (1 : ℚ) / ((k : ℚ) - 2) ^ 2 - 1 / (k : ℚ) ^ 2 =
      (4 * (k : ℚ) - 4) / (((k : ℚ) - 2) ^ 2 * (k : ℚ) ^ 2) := by
    field_simp
    ring
  have h4 : (4 : ℚ) / (k : ℚ) ^ 3 ≤ 1 / ((k : ℚ) - 2) ^ 2 - 1 / (k : ℚ) ^ 2 := by
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3k : (0 : ℚ) ≤ 4 * (k : ℚ) ^ 2 * (3 * (k : ℚ) - 4) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith [h3k]
  have h4' : (4:ℚ) * (1/(k:ℚ)^3) ≤ 1/((k:ℚ)-2)^2-1/(k:ℚ)^2 := by
    simpa only [mul_one_div] using h4
  linarith [h4']

private theorem sum_inv_cube_le (s : Finset ℕ) (m : ℕ) (hm_odd : Odd m)
    (hs : ∀ p ∈ s, Odd p ∧ m ≤ p) :
    ∑ p ∈ s, (1 : ℚ) / (p : ℚ) ^ 3 ≤ 1 / (m : ℚ) ^ 3 + 1 / (4 * (m : ℚ) ^ 2) := by
  have hm1 : 1 ≤ m := by
    obtain ⟨u, hu⟩ := hm_odd
    omega
  have hm0 : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
  have hφ_eq : ∀ p ∈ s, p = m + 2 * ((p - m) / 2) := by
    intro p hp
    obtain ⟨hpo, hmp⟩ := hs p hp
    obtain ⟨u, hu⟩ := hm_odd
    obtain ⟨v, hv⟩ := hpo
    have hev : Even (p - m) := ⟨v - u, by omega⟩
    obtain ⟨w, hw⟩ := hev
    omega
  have hinj : Set.InjOn (fun p => (p - m) / 2) (↑s : Set ℕ) := by
    intro p₁ hp₁ p₂ hp₂ heq
    have e1 := hφ_eq p₁ (Finset.mem_coe.mp hp₁)
    have e2 := hφ_eq p₂ (Finset.mem_coe.mp hp₂)
    have heq' : (p₁ - m) / 2 = (p₂ - m) / 2 := heq
    omega
  have hMbound : ∀ p ∈ s, p ≤ ∑ p ∈ s, p := by
    intro p hp
    exact Finset.single_le_sum (f := fun x => x) (fun i _ => Nat.zero_le i) hp
  obtain ⟨M, hM⟩ : ∃ M, ∀ p ∈ s, p ≤ M := ⟨∑ p ∈ s, p, hMbound⟩
  have himg : s.image (fun p => (p - m) / 2) ⊆ Finset.range (M + 1) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨p, hp, heq⟩ := hi
    have heq' : (p - m) / 2 = i := heq
    rw [Finset.mem_range, ← heq']
    have h1 := hM p hp
    have h2 := hφ_eq p hp
    omega
  have hsum_eq : ∑ p ∈ s, (1 : ℚ) / (p : ℚ) ^ 3 =
      ∑ i ∈ s.image (fun p => (p - m) / 2), (1 : ℚ) / ((m + 2 * i : ℕ) : ℚ) ^ 3 := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro p hp
    have e : (p : ℚ) = ((m + 2 * ((p - m) / 2) : ℕ) : ℚ) := by
      exact_mod_cast hφ_eq p hp
    rw [e]
  rw [hsum_eq]
  have hnn : ∀ i ∈ Finset.range (M + 1), i ∉ s.image (fun p => (p - m) / 2) →
      (0 : ℚ) ≤ 1 / ((m + 2 * i : ℕ) : ℚ) ^ 3 := by
    intro i _ _
    positivity
  have hsub : ∑ i ∈ s.image (fun p => (p - m) / 2), (1:ℚ)/((m+2*i:ℕ):ℚ)^3 ≤
      ∑ i ∈ Finset.range (M + 1), (1:ℚ)/((m+2*i:ℕ):ℚ)^3 :=
    Finset.sum_le_sum_of_subset_of_nonneg himg hnn
  refine hsub.trans ?_
  have hrange : ∑ i ∈ Finset.range (M + 1), (1:ℚ)/((m+2*i:ℕ):ℚ)^3 ≤
      1/(m:ℚ)^3 + 1/(4*(m:ℚ)^2) := by
    simp only [Finset.sum_range_succ']
    simp only [mul_zero, add_zero]
    have hterm : ∀ k ∈ Finset.range M,
        (1:ℚ)/((m+2*(k+1):ℕ):ℚ)^3 ≤
          (1/((m+2*k:ℕ):ℚ)^2-1/((m+2*(k+1):ℕ):ℚ)^2)/4 := by
      intro k _
      have hk3 : 3 ≤ m + 2 * (k + 1) := by omega
      have hF := one_div_cube_le (m + 2 * (k + 1)) hk3
      have hcast : ((m + 2 * (k + 1) : ℕ):ℚ) - 2 = ((m + 2 * k : ℕ):ℚ) := by
        have hnat : m + 2 * (k + 1) = (m + 2 * k) + 2 := by ring
        rw [hnat]
        push_cast
        ring
      rw [hcast] at hF
      exact hF
    have htail : ∑ k ∈ Finset.range M, (1:ℚ)/((m+2*(k+1):ℕ):ℚ)^3 ≤
        1/(4*(m:ℚ)^2) := by
      have hle : ∑ k ∈ Finset.range M, (1:ℚ)/((m+2*(k+1):ℕ):ℚ)^3 ≤
          ∑ k ∈ Finset.range M,
            ((1/((m+2*k:ℕ):ℚ)^2-1/((m+2*(k+1):ℕ):ℚ)^2)/4) :=
        Finset.sum_le_sum hterm
      have hdiv : ∑ k ∈ Finset.range M,
          ((1/((m+2*k:ℕ):ℚ)^2-1/((m+2*(k+1):ℕ):ℚ)^2)/4) =
          (∑ k ∈ Finset.range M,
            (1/((m+2*k:ℕ):ℚ)^2-1/((m+2*(k+1):ℕ):ℚ)^2))/4 := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
      have htele : ∑ k ∈ Finset.range M,
          (1/((m+2*k:ℕ):ℚ)^2-1/((m+2*(k+1):ℕ):ℚ)^2) =
          1/(m:ℚ)^2 - 1/((m+2*M:ℕ):ℚ)^2 := by
        have h := Finset.sum_range_sub' (fun j : ℕ => (1:ℚ)/((m+2*j:ℕ):ℚ)^2) M
        simpa only [mul_zero, add_zero] using h
      rw [hdiv, htele] at hle
      have hM0 : (0:ℚ) ≤ 1/((m+2*M:ℕ):ℚ)^2 := by positivity
      have h2 : ((1:ℚ)/(m:ℚ)^2)/4 = 1/(4*(m:ℚ)^2) := by
        simp only [div_eq_mul_inv, one_mul, mul_inv]
        ring
      have heq : (1/(m:ℚ)^2-1/((m+2*M:ℕ):ℚ)^2)/4 ≤ 1/(4*(m:ℚ)^2) := by
        linarith [hM0, h2]
      exact hle.trans heq
    linarith [htail]
  exact hrange

private theorem prod_one_add_le (s : Finset ℕ) (x : ℕ → ℚ) :
    (∀ p ∈ s, 0 ≤ x p) → ∑ p ∈ s, x p < 1 →
    ∏ p ∈ s, (1 + x p) ≤ 1 / (1 - ∑ p ∈ s, x p) := by
  induction s using Finset.induction with
  | empty => intro _ _; simp
  | insert a t hat ih =>
    intro hx0 hx1
    have hx0t : ∀ p ∈ t, 0 ≤ x p := fun p hp => hx0 p (Finset.mem_insert_of_mem hp)
    have hxa0 : (0:ℚ) ≤ x a := hx0 a (Finset.mem_insert_self a t)
    have hsumt : ∑ p ∈ t, x p ≤ ∑ p ∈ insert a t, x p := by
      rw [Finset.sum_insert hat]
      linarith
    have hx1t : ∑ p ∈ t, x p < 1 := lt_of_le_of_lt hsumt hx1
    have ih' := ih hx0t hx1t
    rw [Finset.prod_insert hat, Finset.sum_insert hat]
    have hSt0 : (0:ℚ) ≤ ∑ p ∈ t, x p := Finset.sum_nonneg hx0t
    have h1 : (0:ℚ) < 1 - ∑ p ∈ t, x p := by linarith
    have h2 : (0:ℚ) < 1 - (x a + ∑ p ∈ t, x p) := by
      have hlt : x a + ∑ p ∈ t, x p < 1 := by
        rwa [Finset.sum_insert hat] at hx1
      linarith
    have hmul : (1 + x a) * ∏ p ∈ t, (1 + x p) ≤
        (1 + x a) * (1 / (1 - ∑ p ∈ t, x p)) :=
      mul_le_mul_of_nonneg_left ih' (by linarith)
    refine hmul.trans ?_
    rw [le_div_iff₀ h2]
    have hSt1 : (1:ℚ) - ∑ p ∈ t, x p ≠ 0 := ne_of_gt h1
    field_simp
    nlinarith [mul_nonneg hxa0 hSt0, sq_nonneg (x a), hxa0, hSt0]

private theorem combine_le (u S C : ℚ) (hu0 : 0 ≤ u)
    (hy : u + S ≤ C / (1 + C)) (hC0 : 0 < C) (B : ℚ)
    (hB : B ≤ 1 / (1 - S)) :
    (1 + u) * B ≤ 1 + C := by
  have hC1 : (0:ℚ) < 1 + C := by linarith
  have hCC : C / (1 + C) < 1 := by
    rw [div_lt_one hC1]
    linarith
  have hy1 : u + S < 1 := lt_of_le_of_lt hy hCC
  have hS1 : S < 1 := by linarith
  have h1S : (0:ℚ) < 1 - S := by linarith
  have h1u : (0:ℚ) ≤ 1 + u := by linarith
  have hBB : (1 + u) * B ≤ (1 + u) * (1 / (1 - S)) :=
    mul_le_mul_of_nonneg_left hB h1u
  have h1 : (u + S) * (1 + C) ≤ C := by
    have h2 := mul_le_mul_of_nonneg_right hy hC1.le
    rwa [div_mul_cancel₀ _ hC1.ne'] at h2
  refine hBB.trans ?_
  rw [mul_one_div, div_le_iff₀ h1S]
  nlinarith [h1, mul_nonneg hu0 hC0.le]

private theorem one_div_sub_one_le (p : ℕ) (hp : 3 ≤ p) :
    (1 : ℚ) / ((p : ℚ) ^ 3 - 1) ≤ (27 / 26) / (p : ℚ) ^ 3 := by
  have hpR : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℚ) < p := by linarith
  have h27 : (27 : ℚ) ≤ (p : ℚ) ^ 3 := by
    calc (27:ℚ) = (3:ℚ)^3 := by norm_num
      _ ≤ (p:ℚ)^3 := pow_le_pow_left₀ (show (0:ℚ) ≤ 3 by norm_num) hpR 3
  have h1 : (0:ℚ) < (p:ℚ)^3-1 := by linarith
  have h2 : (0:ℚ) < (p:ℚ)^3 := pow_pos hp0 3
  rw [div_le_div_iff₀ h1 h2]
  linarith [h27]

private theorem prod_le_one_add (n j : ℕ) (hodd : Odd n) (hperf : n.Perfect)
    (hjmem : j ∈ n.primeFactors) (h2m : 2 * n.minFac ≤ j + 1) :
    (j : ℚ) ^ 2 / ((j : ℚ) ^ 2 - 1) *
        ∏ p ∈ n.primeFactors.erase j, (p : ℚ) ^ 3 / ((p : ℚ) ^ 3 - 1) ≤
      1 + 9 / (8 * (n.minFac : ℚ) ^ 2) := by
  set s : Finset ℕ := n.primeFactors.erase j with hs_def
  have hm3 : 3 ≤ n.minFac := minFac_ge_three n hodd hperf
  have hmR : (3:ℚ) ≤ n.minFac := by exact_mod_cast hm3
  have hm0 : (0:ℚ) < n.minFac := by linarith
  have hm0' : (n.minFac:ℚ) ≠ 0 := ne_of_gt hm0
  have hjprime : j.Prime := Nat.prime_of_mem_primeFactors hjmem
  have hj2 : 2 ≤ j := hjprime.two_le
  have hjR : (2:ℚ) ≤ j := by exact_mod_cast hj2
  have hj0 : (0:ℚ) < j := by linarith
  have hmodd : Odd n.minFac := by
    have hn1 : n ≠ 1 := by
      rintro rfl
      simp at hm3
    have hpmem : n.minFac ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime hn1, Nat.minFac_dvd n, hperf.2.ne'⟩
    exact odd_of_mem_primeFactors n n.minFac hodd hpmem
  have hs_mem : ∀ p ∈ s, Odd p ∧ n.minFac ≤ p := by
    intro p hp
    rw [hs_def] at hp
    have hpm : p ∈ n.primeFactors := Finset.mem_of_mem_erase hp
    refine ⟨odd_of_mem_primeFactors n p hodd hpm, ?_⟩
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpm
    exact Nat.minFac_le_of_dvd hpp.two_le (Nat.dvd_of_mem_primeFactors hpm)
  have hsum3 : ∑ p ∈ s, (1:ℚ)/(p:ℚ)^3 ≤
      1/(n.minFac:ℚ)^3+1/(4*(n.minFac:ℚ)^2) :=
    sum_inv_cube_le s n.minFac hmodd hs_mem
  have hS_le : ∑ p ∈ s, (1:ℚ)/((p:ℚ)^3-1) ≤
      (27/26)*(1/(n.minFac:ℚ)^3+1/(4*(n.minFac:ℚ)^2)) := by
    have hterm : ∀ p ∈ s, (1:ℚ)/((p:ℚ)^3-1) ≤ (27/26)/((p:ℚ)^3) := by
      intro p hp
      have hp3 : 3 ≤ p := le_trans hm3 (hs_mem p hp).2
      exact one_div_sub_one_le p hp3
    have hle : ∑ p ∈ s, (1:ℚ)/((p:ℚ)^3-1) ≤ ∑ p ∈ s, ((27/26:ℚ)/(p:ℚ)^3) :=
      Finset.sum_le_sum hterm
    have hconv : ∑ p ∈ s, ((27/26:ℚ)/(p:ℚ)^3) =
        (27/26)*(∑ p ∈ s, (1:ℚ)/(p:ℚ)^3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [div_eq_mul_one_div]
    rw [hconv] at hle
    have hle2 := mul_le_mul_of_nonneg_left hsum3 (show (0:ℚ) ≤ 27/26 by norm_num)
    exact hle.trans hle2
  have hu_le : (1:ℚ)/((j:ℚ)^2-1) ≤ 1/(4*(n.minFac:ℚ)*((n.minFac:ℚ)-1)) := by
    have hj_ge : (2*(n.minFac:ℚ)-1) ≤ (j:ℚ) := by
      have hcast : (2:ℚ)*(n.minFac:ℚ) ≤ (j:ℚ)+1 := by exact_mod_cast h2m
      linarith
    have h4pos : (0:ℚ) < 4*(n.minFac:ℚ)*((n.minFac:ℚ)-1) :=
      mul_pos (mul_pos (by norm_num) hm0) (by linarith)
    have hsq : (4*(n.minFac:ℚ)*((n.minFac:ℚ)-1)) ≤ (j:ℚ)^2-1 := by
      have h2m1 : (0:ℚ) ≤ 2*(n.minFac:ℚ)-1 := by linarith
      have hpow := pow_le_pow_left₀ h2m1 hj_ge 2
      linarith [hpow]
    exact one_div_le_one_div_of_le h4pos hsq
  have hb1 : (1:ℚ)/(4*(n.minFac:ℚ)*((n.minFac:ℚ)-1)) ≤ 3/(8*(n.minFac:ℚ)^2) := by
    have d1 : (0:ℚ) < 4*(n.minFac:ℚ)*((n.minFac:ℚ)-1) :=
      mul_pos (mul_pos (by norm_num) hm0) (by linarith)
    have d2 : (0:ℚ) < 8*(n.minFac:ℚ)^2 := mul_pos (by norm_num) (pow_pos hm0 2)
    rw [div_le_div_iff₀ d1 d2]
    have hprod : (0:ℚ) ≤ (n.minFac:ℚ)*((n.minFac:ℚ)-3) :=
      mul_nonneg hm0.le (by linarith)
    linarith [hprod]
  have hb2a : (1:ℚ)/(n.minFac:ℚ)^3 ≤ 1/(3*(n.minFac:ℚ)^2) := by
    refine one_div_le_one_div_of_le ?_ ?_
    · exact mul_pos (by norm_num) (pow_pos hm0 2)
    · have hprod : (0:ℚ) ≤ (n.minFac:ℚ)^2*((n.minFac:ℚ)-3) :=
        mul_nonneg (sq_nonneg _) (by linarith)
      linarith [hprod]
  have hb2 : (27/26:ℚ)*((1:ℚ)/(n.minFac:ℚ)^3+1/(4*(n.minFac:ℚ)^2)) ≤
      (27/26)*(1/(3*(n.minFac:ℚ)^2)+1/(4*(n.minFac:ℚ)^2)) := by
    apply mul_le_mul_of_nonneg_left _ (show (0:ℚ) ≤ 27/26 by norm_num)
    linarith [hb2a]
  have hb3 : (3:ℚ)/(8*(n.minFac:ℚ)^2) +
      (27/26)*(1/(3*(n.minFac:ℚ)^2)+1/(4*(n.minFac:ℚ)^2)) = 51/(52*(n.minFac:ℚ)^2) := by
    have hC' : (n.minFac:ℚ)^2 ≠ 0 := pow_ne_zero 2 hm0'
    field_simp
    ring
  have hy51 : (1:ℚ)/((j:ℚ)^2-1) + ∑ p ∈ s, (1:ℚ)/((p:ℚ)^3-1) ≤
      51/(52*(n.minFac:ℚ)^2) := by
    calc (1:ℚ)/((j:ℚ)^2-1) + ∑ p ∈ s, (1:ℚ)/((p:ℚ)^3-1)
        ≤ 1/(4*(n.minFac:ℚ)*((n.minFac:ℚ)-1)) +
            (27/26)*(1/(n.minFac:ℚ)^3+1/(4*(n.minFac:ℚ)^2)) :=
          add_le_add hu_le hS_le
      _ ≤ 3/(8*(n.minFac:ℚ)^2) + (27/26)*(1/(3*(n.minFac:ℚ)^2)+1/(4*(n.minFac:ℚ)^2)) :=
          add_le_add hb1 hb2
      _ = 51/(52*(n.minFac:ℚ)^2) := hb3
  have hb4 : (51:ℚ)/(52*(n.minFac:ℚ)^2) ≤ 9/(8*(n.minFac:ℚ)^2+9) := by
    have d1 : (0:ℚ) < 52*(n.minFac:ℚ)^2 := mul_pos (by norm_num) (pow_pos hm0 2)
    have d2 : (0:ℚ) < 8*(n.minFac:ℚ)^2+9 := by
      have hnn : (0:ℚ) ≤ 8*(n.minFac:ℚ)^2 :=
        mul_nonneg (by norm_num) (sq_nonneg _)
      linarith
    rw [div_le_div_iff₀ d1 d2]
    have h9 : (9:ℚ) ≤ (n.minFac:ℚ)^2 := by linarith [sq_nonneg ((n.minFac:ℚ)-3)]
    linarith [h9]
  have hCeq : (9:ℚ)/(8*(n.minFac:ℚ)^2+9) =
      (9/(8*(n.minFac:ℚ)^2)) / (1 + 9/(8*(n.minFac:ℚ)^2)) := by
    have h8 : (8:ℚ)*(n.minFac:ℚ)^2 ≠ 0 :=
      ne_of_gt (mul_pos (by norm_num) (pow_pos hm0 2))
    have h89 : (8:ℚ)*(n.minFac:ℚ)^2+9 ≠ 0 := by
      have hnn : (0:ℚ) ≤ 8*(n.minFac:ℚ)^2 :=
        mul_nonneg (by norm_num) (sq_nonneg _)
      have hpos : (0:ℚ) < 8*(n.minFac:ℚ)^2+9 := by linarith
      linarith
    field_simp
  have hy : (1:ℚ)/((j:ℚ)^2-1) + ∑ p ∈ s, (1:ℚ)/((p:ℚ)^3-1) ≤
      (9/(8*(n.minFac:ℚ)^2)) / (1 + 9/(8*(n.minFac:ℚ)^2)) := by
    rw [← hCeq]
    exact hy51.trans hb4
  have hC0 : (0:ℚ) < 9/(8*(n.minFac:ℚ)^2) :=
    div_pos (by norm_num) (mul_pos (by norm_num) (pow_pos hm0 2))
  have hu0 : (0:ℚ) ≤ 1/((j:ℚ)^2-1) := by
    apply one_div_nonneg.mpr
    have h4 : (4:ℚ) ≤ (j:ℚ)^2 := by
      calc (4:ℚ) = (2:ℚ)^2 := by norm_num
        _ ≤ (j:ℚ)^2 := pow_le_pow_left₀ (show (0:ℚ) ≤ 2 by norm_num) hjR 2
    linarith
  have hx0 : ∀ p ∈ s, (0:ℚ) ≤ 1/((p:ℚ)^3-1) := by
    intro p hp
    apply one_div_nonneg.mpr
    have hp3 : (3:ℚ) ≤ p := by exact_mod_cast le_trans hm3 (hs_mem p hp).2
    have h27 : (27:ℚ) ≤ (p:ℚ)^3 := by
      calc (27:ℚ) = (3:ℚ)^3 := by norm_num
        _ ≤ (p:ℚ)^3 := pow_le_pow_left₀ (show (0:ℚ) ≤ 3 by norm_num) hp3 3
    linarith
  have hS1 : ∑ p ∈ s, (1:ℚ)/((p:ℚ)^3-1) < 1 := by
    have hCC : (9/(8*(n.minFac:ℚ)^2)) / (1 + 9/(8*(n.minFac:ℚ)^2)) < 1 := by
      rw [div_lt_one (by linarith : (0:ℚ) < 1 + 9/(8*(n.minFac:ℚ)^2))]
      linarith
    have hlt := lt_of_le_of_lt hy hCC
    linarith
  have hBle : ∏ p ∈ s, (1 + (1:ℚ)/((p:ℚ)^3-1)) ≤
      1/(1-∑ p ∈ s, (1:ℚ)/((p:ℚ)^3-1)) :=
    prod_one_add_le s _ hx0 hS1
  have hfactorA : (j:ℚ)^2/((j:ℚ)^2-1) = 1 + (1:ℚ)/((j:ℚ)^2-1) := by
    have hne : (j:ℚ)^2-1 ≠ 0 := by
      have h4 : (4:ℚ) ≤ (j:ℚ)^2 := by
        calc (4:ℚ) = (2:ℚ)^2 := by norm_num
          _ ≤ (j:ℚ)^2 := pow_le_pow_left₀ (show (0:ℚ) ≤ 2 by norm_num) hjR 2
      have hpos : (0:ℚ) < (j:ℚ)^2-1 := by linarith
      linarith
    have heq : (j:ℚ)^2/((j:ℚ)^2-1) = ((j:ℚ)^2-1+1)/((j:ℚ)^2-1) := by
      rw [sub_add_cancel]
    rw [heq, add_div, div_self hne]
  have hBeq : ∏ p ∈ s, (p:ℚ)^3/((p:ℚ)^3-1) =
      ∏ p ∈ s, (1 + (1:ℚ)/((p:ℚ)^3-1)) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hp3 : (3:ℚ) ≤ p := by exact_mod_cast le_trans hm3 (hs_mem p hp).2
    have hne : (p:ℚ)^3-1 ≠ 0 := by
      have h27 : (27:ℚ) ≤ (p:ℚ)^3 := by
        calc (27:ℚ) = (3:ℚ)^3 := by norm_num
          _ ≤ (p:ℚ)^3 := pow_le_pow_left₀ (show (0:ℚ) ≤ 3 by norm_num) hp3 3
      have hpos : (0:ℚ) < (p:ℚ)^3-1 := by linarith
      linarith
    have heq : (p:ℚ)^3/((p:ℚ)^3-1) = ((p:ℚ)^3-1+1)/((p:ℚ)^3-1) := by
      rw [sub_add_cancel]
    rw [heq, add_div, div_self hne]
  rw [hfactorA, hBeq]
  exact combine_le (1/((j:ℚ)^2-1)) (∑ p ∈ s, 1/((p:ℚ)^3-1)) (9/(8*(n.minFac:ℚ)^2))
    hu0 hy hC0 _ hBle

/-- **Bound on the prime product of an odd perfect number via its least prime factor.** Let $n$ be
an odd perfect number with least prime factor $p_1$, and let $H(n) = \prod_{p \mid n} p/(p-1)$,
the product over the primes $p$ dividing $n$. Then $H(n) \le 2 + \frac{9}{4 p_1^2}$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 5 (`integers-2025-A59-prop-5`). -/
public theorem oddPerfect_abundancySup_le
    (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) :
    abundancySup n ≤ 2 + 9 / (4 * (n.minFac : ℚ) ^ 2) := by
  obtain ⟨j, hjmem, hjodd, heven, h2m⟩ := exists_single_odd_exponent n hodd hperf
  have hdiv := abundancySup_div_abundancyIndex_le_of_single_odd_exponent n j hodd
    hjmem hjodd heven
  have hindex := abundancyIndex_eq_two_of_perfect n hperf
  rw [hindex] at hdiv
  have hpos : (0 : ℚ) < 2 := by norm_num
  have hle : abundancySup n ≤
      ((j : ℚ) ^ 2 / ((j : ℚ) ^ 2 - 1) *
        ∏ p ∈ n.primeFactors.erase j, (p : ℚ) ^ 3 / ((p : ℚ) ^ 3 - 1)) * 2 :=
    (div_le_iff₀ hpos).mp hdiv
  have hanalytic := prod_le_one_add n j hodd hperf hjmem h2m
  have hminpos : (0 : ℚ) < n.minFac := by exact_mod_cast Nat.minFac_pos n
  have h2nn : (0 : ℚ) ≤ 2 := by norm_num
  have hmul := mul_le_mul_of_nonneg_right hanalytic h2nn
  have heq : (1 + 9 / (8 * (n.minFac : ℚ) ^ 2)) * 2 =
      2 + 9 / (4 * (n.minFac : ℚ) ^ 2) := by
    have hx0 : (n.minFac : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hminpos)
    field_simp
    ring
  calc abundancySup n ≤
        ((j : ℚ) ^ 2 / ((j : ℚ) ^ 2 - 1) *
          ∏ p ∈ n.primeFactors.erase j, (p : ℚ) ^ 3 / ((p : ℚ) ^ 3 - 1)) * 2 :=
        hle
      _ ≤ (1 + 9 / (8 * (n.minFac : ℚ) ^ 2)) * 2 := hmul
      _ = 2 + 9 / (4 * (n.minFac : ℚ) ^ 2) := heq

-- Preliminary: primitive non-deficient implies n ≥ 2
private theorem two_le_of_prim (n : ℕ) (hn : IsPrimitiveNondeficient n) : 2 ≤ n := by
  obtain ⟨⟨hn0, hsum⟩, _⟩ := hn
  by_contra h
  have hlt : n < 2 := lt_of_not_ge h
  have h01 : n = 0 ∨ n = 1 := by omega
  rcases h01 with rfl | rfl
  · exact absurd rfl hn0
  · have h1 : ∑ d ∈ Nat.divisors 1, d = 1 := by decide
    omega

-- minFac is prime and in primeFactors
private theorem minFac_mem (n : ℕ) (hn2 : 2 ≤ n) : n.minFac ∈ n.primeFactors := by
  have hn1 : n ≠ 1 := by omega
  have hprime : n.minFac.Prime := Nat.minFac_prime hn1
  have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hn0 : n ≠ 0 := by omega
  exact Nat.mem_primeFactors.mpr ⟨hprime, hdvd, hn0⟩

private theorem minFac_ge_two (n : ℕ) (hn2 : 2 ≤ n) : 2 ≤ n.minFac := by
  have hn1 : n ≠ 1 := by omega
  exact (Nat.minFac_prime hn1).two_le

private theorem minFac_le_of_mem (n p : ℕ) (hp : p ∈ n.primeFactors) : n.minFac ≤ p := by
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  exact Nat.minFac_le_of_dvd hprime.two_le hdvd

private theorem factor_pos (n p : ℕ) (hn0 : n ≠ 0) (hp : p ∈ n.primeFactors) :
    0 < n.factorization p := by
  have h := Nat.mem_primeFactors.mp hp
  exact Nat.Prime.factorization_pos_of_dvd h.1 hn0 h.2.1

-- 1 ≤ abundancyIndex for positive n
private theorem one_le_abund (n : ℕ) (hn : 0 < n) : 1 ≤ abundancyIndex n := by
  rw [abundancyIndex, one_le_div (by exact_mod_cast hn)]
  exact_mod_cast Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors_self n hn.ne')

-- abundancyIndex of proper deficient divisor is < 2
private theorem abund_lt_two_of_def (m : ℕ) (hm0 : m ≠ 0)
    (hdef : ∑ d ∈ Nat.divisors m, d < 2 * m) : abundancyIndex m < 2 := by
  have hmR : (0 : ℚ) < (m : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
  rw [abundancyIndex, div_lt_iff₀ hmR]
  have hcast : ((∑ d ∈ Nat.divisors m, d : ℕ) : ℚ) < ((2 * m : ℕ) : ℚ) := by
    exact_mod_cast hdef
  push_cast at hcast ⊢
  linarith

-- n / p is a proper divisor
private theorem div_mem_divisors (n p : ℕ) (hn0 : n ≠ 0) (hpdvd : p ∣ n) :
    n / p ∈ Nat.divisors n :=
  Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hpdvd, hn0⟩

private theorem div_lt_self_of_dvd (n p : ℕ) (hn : 0 < n) (hp1 : 1 < p) : n / p < n :=
  Nat.div_lt_self hn hp1

private theorem div_pos_of_dvd (n p : ℕ) (hn : 0 < n) (hpdvd : p ∣ n) (hp0 : 0 < p) :
    0 < n / p :=
  Nat.div_pos (Nat.le_of_dvd hn hpdvd) hp0

-- p^a ≥ p for a ≥ 1
private theorem pow_ge_self (p a : ℕ) (hp : 2 ≤ p) (ha : 1 ≤ a) : p ≤ p ^ a := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  simp only [Nat.add_comm 1 b, pow_succ]
  have hb : 1 ≤ p ^ b := Nat.one_le_pow b p (by omega)
  calc p = p * 1 := (mul_one p).symm
    _ ≤ p * p ^ b := Nat.mul_le_mul_left p hb
    _ = p ^ b * p := mul_comm _ _

-- Main h bound: h(n) < 2 + 2/p1
private theorem abund_lt (n : ℕ) (hn : IsPrimitiveNondeficient n) :
    abundancyIndex n < 2 + 2 / (n.minFac : ℚ) := by
  have hn2 : 2 ≤ n := two_le_of_prim n hn
  obtain ⟨⟨hn0, hsum⟩, hprim⟩ := hn
  have hn_pos : 0 < n := by omega
  have hp1_mem : n.minFac ∈ n.primeFactors := minFac_mem n hn2
  have hp1_prime : n.minFac.Prime := Nat.prime_of_mem_primeFactors hp1_mem
  have hp1_ge2 : 2 ≤ n.minFac := hp1_prime.two_le
  have hpdvd : n.minFac ∣ n := Nat.dvd_of_mem_primeFactors hp1_mem
  have ha_pos : 0 < n.factorization n.minFac := factor_pos n n.minFac hn0 hp1_mem
  have ha1 : 1 ≤ n.factorization n.minFac := ha_pos
  have hdiv_mem : n / n.minFac ∈ Nat.divisors n := div_mem_divisors n n.minFac hn0 hpdvd
  have hdiv_lt : n / n.minFac < n := div_lt_self_of_dvd n n.minFac hn_pos hp1_prime.one_lt
  have hdiv_pos : 0 < n / n.minFac := div_pos_of_dvd n n.minFac hn_pos hpdvd hp1_prime.pos
  have hdef := hprim _ hdiv_mem hdiv_lt
  have hdiv_ne : n / n.minFac ≠ 0 := by omega
  have h_small : abundancyIndex (n / n.minFac) < 2 :=
    abund_lt_two_of_def _ hdiv_ne hdef
  have h_big_pos : 0 < abundancyIndex (n / n.minFac) :=
    zero_lt_one.trans_le (one_le_abund _ hdiv_pos)
  have hratio := abundancyIndex_div_le n n.minFac (n.factorization n.minFac)
    hn_pos hp1_prime ha1 rfl
  have hpow_ge : n.minFac ≤ n.minFac ^ n.factorization n.minFac :=
    pow_ge_self _ _ hp1_ge2 ha1
  have hp1Q_pos : (0 : ℚ) < (n.minFac : ℚ) := by exact_mod_cast hp1_prime.pos
  have hpowQ_ge : (n.minFac : ℚ) ≤ ((n.minFac ^ n.factorization n.minFac : ℕ) : ℚ) := by
    exact_mod_cast hpow_ge
  have hpowQ_eq : ((n.minFac ^ n.factorization n.minFac : ℕ) : ℚ) =
      (n.minFac : ℚ) ^ n.factorization n.minFac := by push_cast; ring
  -- h(n) = (h(n)/h(n/p)) * h(n/p)
  have h_eq : abundancyIndex n =
      (abundancyIndex n / abundancyIndex (n / n.minFac)) *
        abundancyIndex (n / n.minFac) := by
    field_simp
  rw [h_eq]
  have h1 : abundancyIndex n / abundancyIndex (n / n.minFac) ≤
      1 + 1 / (n.minFac : ℚ) ^ n.factorization n.minFac := hratio
  have h2 : (1 : ℚ) + 1 / (n.minFac : ℚ) ^ n.factorization n.minFac ≤
      1 + 1 / (n.minFac : ℚ) := by
    have hle : (1 : ℚ) / (n.minFac : ℚ) ^ n.factorization n.minFac ≤ 1 / (n.minFac : ℚ) := by
      rw [← hpowQ_eq]
      exact one_div_le_one_div_of_le hp1Q_pos hpowQ_ge
    linarith
  have h_ratio_le : abundancyIndex n / abundancyIndex (n / n.minFac) ≤
      1 + 1 / (n.minFac : ℚ) := h1.trans h2
  have h_nonneg : 0 ≤ abundancyIndex n / abundancyIndex (n / n.minFac) := by
    apply div_nonneg _ (le_of_lt h_big_pos)
    exact le_trans zero_le_one (one_le_abund _ hn_pos)
  -- (ratio) * h(n/p) < (1+1/p1) * 2
  have hpos2 : (0 : ℚ) < 1 + 1 / (n.minFac : ℚ) := by positivity
  have h_bound : (abundancyIndex n / abundancyIndex (n / n.minFac)) *
      abundancyIndex (n / n.minFac) < (1 + 1 / (n.minFac : ℚ)) * 2 := by
    have hstep1 : (abundancyIndex n / abundancyIndex (n / n.minFac)) *
        abundancyIndex (n / n.minFac) ≤ (1 + 1 / (n.minFac : ℚ)) *
        abundancyIndex (n / n.minFac) :=
      mul_le_mul_of_nonneg_right h_ratio_le (le_of_lt h_big_pos)
    have hstep2 : (1 + 1 / (n.minFac : ℚ)) * abundancyIndex (n / n.minFac) <
        (1 + 1 / (n.minFac : ℚ)) * 2 :=
      mul_lt_mul_of_pos_left h_small hpos2
    exact lt_of_le_of_lt hstep1 hstep2
  calc (abundancyIndex n / abundancyIndex (n / n.minFac)) *
        abundancyIndex (n / n.minFac)
      < (1 + 1 / (n.minFac : ℚ)) * 2 := h_bound
    _ = 2 + 2 / (n.minFac : ℚ) := by ring

-- h < 3 corollary
private theorem abund_lt_three (n : ℕ) (hn : IsPrimitiveNondeficient n) :
    abundancyIndex n < 3 := by
  have hn2 : 2 ≤ n := two_le_of_prim n hn
  have hp1_ge2 : 2 ≤ n.minFac := minFac_ge_two n hn2
  have hp1Q_pos : (0 : ℚ) < (n.minFac : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hp1Q_ge : (2 : ℚ) ≤ (n.minFac : ℚ) := by exact_mod_cast hp1_ge2
  have h1 : (2 : ℚ) / (n.minFac : ℚ) ≤ 1 := by
    rw [div_le_one hp1Q_pos]
    linarith
  have h2 := abund_lt n hn
  linarith

-- 1 + sum ≤ prod (1 + .) for nonnegative f
private theorem one_add_sum_le_prod (s : Finset ℕ) (f : ℕ → ℚ)
    (hf : ∀ p ∈ s, 0 ≤ f p) : 1 + ∑ p ∈ s, f p ≤ ∏ p ∈ s, (1 + f p) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t hat IH =>
    have hf_a : 0 ≤ f a := hf a (Finset.mem_insert_self a t)
    have hf_t : ∀ p ∈ t, 0 ≤ f p := fun p hp => hf p (Finset.mem_insert_of_mem hp)
    have hIH := IH hf_t
    have hprod_ge_one : (1 : ℚ) ≤ ∏ p ∈ t, (1 + f p) := by
      apply Finset.one_le_prod₀
      intro p hp
      linarith [hf_t p hp]
    have hfa_le : f a ≤ (∏ p ∈ t, (1 + f p)) * f a := by
      have : (1 : ℚ) * f a ≤ (∏ p ∈ t, (1 + f p)) * f a :=
        mul_le_mul_of_nonneg_right hprod_ge_one hf_a
      simpa using this
    rw [Finset.sum_insert hat, Finset.prod_insert hat]
    have h_add := add_le_add hIH hfa_le
    have h_eq1 : (1 + ∑ p ∈ t, f p) + f a = 1 + (f a + ∑ p ∈ t, f p) := by ring
    have h_eq2 : (∏ p ∈ t, (1 + f p)) + (∏ p ∈ t, (1 + f p)) * f a =
        (1 + f a) * (∏ p ∈ t, (1 + f p)) := by ring
    rw [h_eq1, h_eq2] at h_add
    exact h_add

-- h as a product over prime factors
private theorem abund_eq_prod (n : ℕ) (hn : n ≠ 0) :
    abundancyIndex n = ∏ p ∈ n.primeFactors,
      (((∑ k ∈ Finset.range (n.factorization p + 1), p ^ k : ℕ)) : ℚ) /
        (p : ℚ) ^ n.factorization p := by
  have hprod : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn
  rw [abundancyIndex, ← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn, hprod]
  simp only [mul_one, Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, ← Finset.prod_div_distrib]

-- Each factor is at least 1 + 1/p
private theorem factor_ge_one_add (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) :
    (1 : ℚ) + 1 / (p : ℚ) ≤
      (((∑ k ∈ Finset.range (a + 1), p ^ k : ℕ)) : ℚ) / (p : ℚ) ^ a := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  simp only [Nat.add_comm 1 b] at ha ⊢
  -- a = b + 1, so range (b+2) contains b and b+1
  have hpQ_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.pos
  have hpow_pos : (0 : ℚ) < (p : ℚ) ^ (b + 1) := pow_pos hpQ_pos _
  have hpow_ne : (p : ℚ) ^ (b + 1) ≠ 0 := ne_of_gt hpow_pos
  have hpb_ne : (p : ℚ) ^ b ≠ 0 := pow_ne_zero _ (ne_of_gt hpQ_pos)
  -- sum in ℕ is at least p^(b+1) + p^b
  have hsum_ge : p ^ (b + 1) + p ^ b ≤ ∑ k ∈ Finset.range (b + 1 + 1), p ^ k := by
    have hsub : ({b, b + 1} : Finset ℕ) ⊆ Finset.range (b + 1 + 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_range]
      omega
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => Nat.zero_le (p ^ i))
    have hsum_pair : ∑ k ∈ ({b, b + 1} : Finset ℕ), p ^ k = p ^ b + p ^ (b + 1) := by
      rw [Finset.sum_pair (by omega)]
    rw [hsum_pair] at hle
    linarith [hle]
  have hcast : ((p ^ (b + 1) + p ^ b : ℕ) : ℚ) ≤
      ((∑ k ∈ Finset.range (b + 1 + 1), p ^ k : ℕ) : ℚ) := by
    exact_mod_cast hsum_ge
  push_cast at hcast ⊢
  rw [le_div_iff₀ hpow_pos]
  -- goal: (1 + 1/p) * p^(b+1) ≤ sum; have p^(b+1) + p^b ≤ sum
  have h_alg : (1 + 1 / (p : ℚ)) * (p : ℚ) ^ (b + 1) =
      (p : ℚ) ^ (b + 1) + (p : ℚ) ^ b := by
    field_simp
    rw [pow_succ]
    ring
  rw [h_alg]
  exact hcast

-- Product of (1+1/p) is at most h(n)
private theorem prod_le_abund (n : ℕ) (hn0 : n ≠ 0) :
    ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℚ)) ≤ abundancyIndex n := by
  rw [abund_eq_prod n hn0]
  apply Finset.prod_le_prod₀ _ _
  · intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpQ_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hprime.pos
    positivity
  · intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have ha : 1 ≤ n.factorization p := factor_pos n p hn0 hp
    exact factor_ge_one_add p _ hprime ha

-- T(n) = sum 1/p is less than 2
private theorem sum_inv_lt_two (n : ℕ) (hn : IsPrimitiveNondeficient n) :
    ∑ p ∈ n.primeFactors, (1 : ℚ) / (p : ℚ) < 2 := by
  have h3 : abundancyIndex n < 3 := abund_lt_three n hn
  obtain ⟨⟨hn0, hsum⟩, hprim⟩ := hn
  have h1 : (1 : ℚ) + ∑ p ∈ n.primeFactors, (1 : ℚ) / (p : ℚ) ≤
      ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℚ)) := by
    apply one_add_sum_le_prod
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpQ_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hprime.pos
    positivity
  have h2 : ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℚ)) ≤ abundancyIndex n :=
    prod_le_abund n hn0
  linarith

-- H/h as a product (copied from AbundancySupDivIndex)
private def primePowerRatio (p k : ℕ) : ℚ := (p : ℚ) ^ k / ((p : ℚ) ^ k - 1)

private theorem ratio_eq_prod {n : ℕ} (hn : n ≠ 0) :
    abundancySup n / abundancyIndex n =
      ∏ p ∈ n.primeFactors, primePowerRatio p (n.factorization p + 1) := by
  have hprod : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn
  rw [abundancyIndex, abundancySup, ← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn, hprod]
  simp only [mul_one, Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [div_div_div_eq, mul_geom_sum, ← pow_succ', primePowerRatio]

-- p^(a+1) ≥ 4 for prime p and a ≥ 1
private theorem pow_succ_ge_four (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) :
    4 ≤ p ^ (a + 1) := by
  have hp2 : 2 ≤ p := hp.two_le
  have h1 : p ^ 2 ≤ p ^ (a + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp2 2
  norm_num at h2 ⊢
  linarith [h1, h2]

-- primePowerRatio = 1 + 1/(p^k - 1)
private theorem ratio_eq_one_add (p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k) :
    primePowerRatio p k = 1 + 1 / ((p : ℚ) ^ k - 1) := by
  have hpQ : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.one_lt
  have hlt : (1 : ℚ) < (p : ℚ) ^ k := one_lt_pow₀ hpQ (by omega)
  have hne : (p : ℚ) ^ k - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
  rw [primePowerRatio]
  field_simp
  ring

-- y_p = 1/(p^(a+1) - 1) is nonnegative
private theorem y_nonneg (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) :
    0 ≤ (1 : ℚ) / ((p : ℚ) ^ (a + 1) - 1) := by
  have hpQ : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.one_lt
  have hlt : (1 : ℚ) < (p : ℚ) ^ (a + 1) := one_lt_pow₀ hpQ (by omega)
  have hpos : (0 : ℚ) < (p : ℚ) ^ (a + 1) - 1 := sub_pos.mpr hlt
  positivity

-- y_p ≤ 2 / p^(a+1)
private theorem y_le_two_div_pow (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) :
    (1 : ℚ) / ((p : ℚ) ^ (a + 1) - 1) ≤ 2 / (p : ℚ) ^ (a + 1) := by
  have hpQ : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.one_lt
  have hX : (2 : ℚ) ≤ (p : ℚ) ^ (a + 1) := by
    have h4 : (4 : ℚ) ≤ (p : ℚ) ^ (a + 1) := by
      have h4n : 4 ≤ p ^ (a + 1) := pow_succ_ge_four p a hp ha
      have hcast : ((4 : ℕ) : ℚ) ≤ ((p ^ (a + 1) : ℕ) : ℚ) := by exact_mod_cast h4n
      push_cast at hcast ⊢
      linarith [hcast]
    linarith
  have hpos : (0 : ℚ) < (p : ℚ) ^ (a + 1) - 1 := by linarith
  have hposX : (0 : ℚ) < (p : ℚ) ^ (a + 1) := by linarith
  rw [div_le_div_iff₀ hpos hposX]
  nlinarith [hX]

-- p^(a+1) ≥ p^2
private theorem pow_succ_ge_sq (p a : ℕ) (hp : 1 ≤ p) (ha : 1 ≤ a) :
    (p : ℚ) ^ 2 ≤ (p : ℚ) ^ (a + 1) := by
  apply pow_le_pow_right₀ (by exact_mod_cast hp) (by omega)

-- 2/p^(a+1) ≤ 2/p^2
private theorem two_div_pow_le (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) :
    (2 : ℚ) / (p : ℚ) ^ (a + 1) ≤ 2 / (p : ℚ) ^ 2 := by
  have hpQ : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.one_le
  have hle : (p : ℚ) ^ 2 ≤ (p : ℚ) ^ (a + 1) := pow_succ_ge_sq p a hp.one_le ha
  have hpos2 : (0 : ℚ) < (p : ℚ) ^ 2 := by positivity
  apply div_le_div_of_nonneg_left (by norm_num) hpos2 hle

-- 1/p^2 ≤ (1/p1)*(1/p) for p ≥ p1
private theorem inv_sq_le (p p1 : ℕ) (hp : p.Prime) (hle : p1 ≤ p) (hp1 : 2 ≤ p1) :
    (1 : ℚ) / (p : ℚ) ^ 2 ≤ (1 / (p1 : ℚ)) * (1 / (p : ℚ)) := by
  have hpQ_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.pos
  have hp1Q_pos : (0 : ℚ) < (p1 : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hleQ : (p1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hle
  have h_inv_le : (1 : ℚ) / (p : ℚ) ≤ 1 / (p1 : ℚ) :=
    one_div_le_one_div_of_le hp1Q_pos hleQ
  have h_nonneg : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
  have h_eq : (1 : ℚ) / (p : ℚ) ^ 2 = (1 / (p : ℚ)) * (1 / (p : ℚ)) := by
    rw [div_mul_div_comm]
    simp [pow_two]
  rw [h_eq]
  exact mul_le_mul_of_nonneg_right h_inv_le h_nonneg

-- Sum of 1/p^2 is at most T/p1
private theorem sum_inv_sq_le (n : ℕ) (hn2 : 2 ≤ n) :
    ∑ p ∈ n.primeFactors, (1 : ℚ) / (p : ℚ) ^ 2 ≤
      (1 / (n.minFac : ℚ)) * ∑ p ∈ n.primeFactors, (1 : ℚ) / (p : ℚ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hle : n.minFac ≤ p := minFac_le_of_mem n p hp
  have hp1 : 2 ≤ n.minFac := minFac_ge_two n hn2
  exact inv_sq_le p n.minFac hprime hle hp1

-- Sum of y is less than 4/p1
private theorem sum_y_lt (n : ℕ) (hn : IsPrimitiveNondeficient n) :
    ∑ p ∈ n.primeFactors, (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) <
      4 / (n.minFac : ℚ) := by
  have hn2 : 2 ≤ n := two_le_of_prim n hn
  have hT := sum_inv_lt_two n hn
  have hsq := sum_inv_sq_le n hn2
  have hp1Q_pos : (0 : ℚ) < (n.minFac : ℚ) := by
    have h2 := minFac_ge_two n hn2
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  -- Each y ≤ 2/p^2
  have h_each : ∀ p ∈ n.primeFactors,
      (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) ≤ 2 / (p : ℚ) ^ 2 := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have ha : 1 ≤ n.factorization p := by
      have hn0 : n ≠ 0 := by omega
      exact factor_pos n p hn0 hp
    exact (y_le_two_div_pow p _ hprime ha).trans (two_div_pow_le p _ hprime ha)
  have h_sum_le : ∑ p ∈ n.primeFactors, (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) ≤
      ∑ p ∈ n.primeFactors, (2 : ℚ) / (p : ℚ) ^ 2 :=
    Finset.sum_le_sum h_each
  have h_sum_eq : ∑ p ∈ n.primeFactors, (2 : ℚ) / (p : ℚ) ^ 2 =
      2 * ∑ p ∈ n.primeFactors, (1 : ℚ) / (p : ℚ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [h_sum_eq] at h_sum_le
  have h_bound : (2 : ℚ) * ∑ p ∈ n.primeFactors, (1 : ℚ) / (p : ℚ) ^ 2 <
      4 / (n.minFac : ℚ) := by
    have h1 : ∑ p ∈ n.primeFactors, (1 : ℚ) / (p : ℚ) ^ 2 <
        (1 / (n.minFac : ℚ)) * 2 := by
      have h_nonneg : (0 : ℚ) ≤ 1 / (n.minFac : ℚ) := by positivity
      have h_strict : (1 / (n.minFac : ℚ)) * ∑ p ∈ n.primeFactors, (1 : ℚ) / (p : ℚ) <
          (1 / (n.minFac : ℚ)) * 2 :=
        mul_lt_mul_of_pos_left hT (by positivity)
      exact lt_of_le_of_lt hsq h_strict
    have h2 : (2 : ℚ) * ∑ p ∈ n.primeFactors, (1 : ℚ) / (p : ℚ) ^ 2 <
        2 * ((1 / (n.minFac : ℚ)) * 2) :=
      mul_lt_mul_of_pos_left h1 (by norm_num)
    have h_eq : (2 : ℚ) * ((1 / (n.minFac : ℚ)) * 2) = 4 / (n.minFac : ℚ) := by ring
    rw [h_eq] at h2
    exact h2
  exact lt_of_le_of_lt h_sum_le h_bound

-- Product bound for small sums: if sum ≤ 1/2 then prod (1+y) ≤ 1 + 2*sum
private theorem prod_le_one_add_two_mul (s : Finset ℕ) (f : ℕ → ℚ)
    (hf : ∀ p ∈ s, 0 ≤ f p) (hsum : ∑ p ∈ s, f p ≤ 1 / 2) :
    ∏ p ∈ s, (1 + f p) ≤ 1 + 2 * ∑ p ∈ s, f p := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t hat IH =>
    have hf_a : 0 ≤ f a := hf a (Finset.mem_insert_self a t)
    have hf_t : ∀ p ∈ t, 0 ≤ f p := fun p hp => hf p (Finset.mem_insert_of_mem hp)
    rw [Finset.sum_insert hat] at hsum
    have hsum_t : ∑ p ∈ t, f p ≤ 1 / 2 := by linarith [hf_a]
    have hIH := IH hf_t hsum_t
    have h_nonneg : (0 : ℚ) ≤ 1 + f a := by linarith
    have h_mul_le : (1 + f a) * ∏ p ∈ t, (1 + f p) ≤
        (1 + f a) * (1 + 2 * ∑ p ∈ t, f p) :=
      mul_le_mul_of_nonneg_left hIH h_nonneg
    rw [Finset.prod_insert hat]
    -- (1+f a)*(1+2∑_t) = 1 + 2∑_t + f a + 2 f a ∑_t ≤ 1 + 2(∑_t + f a)
    have h_key : (1 + f a) * (1 + 2 * ∑ p ∈ t, f p) ≤
        1 + 2 * (f a + ∑ p ∈ t, f p) := by
      have h2sum : 2 * ∑ p ∈ t, f p ≤ 1 := by linarith
      have hfa_mul : f a * (2 * ∑ p ∈ t, f p) ≤ f a * 1 :=
        mul_le_mul_of_nonneg_left h2sum hf_a
      nlinarith [hfa_mul, hf_a]
    have h_eq : (1 : ℚ) + 2 * (f a + ∑ p ∈ t, f p) = 1 + 2 * ∑ p ∈ insert a t, f p := by
      rw [Finset.sum_insert hat]
    rw [h_eq] at h_key
    exact h_mul_le.trans h_key

-- H/h = prod (1 + y)
private theorem ratio_eq_prod_one_add (n : ℕ) (hn0 : n ≠ 0) :
    abundancySup n / abundancyIndex n =
      ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℚ) ^ (n.factorization p + 1) - 1)) := by
  rw [ratio_eq_prod hn0]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have ha : 1 ≤ n.factorization p := factor_pos n p hn0 hp
  have hk : 2 ≤ n.factorization p + 1 := by omega
  exact ratio_eq_one_add p _ hprime hk

-- Large p1 case: H < 2 + 34/p1 in ℚ
private theorem abund_sup_lt_large (n : ℕ) (hn : IsPrimitiveNondeficient n)
    (h8 : 8 ≤ n.minFac) : abundancySup n < 2 + 34 / (n.minFac : ℚ) := by
  have hn2 : 2 ≤ n := two_le_of_prim n hn
  obtain ⟨⟨hn0, hsum⟩, hprim⟩ := hn
  have hn_pos : 0 < n := by omega
  have hp1Q_pos : (0 : ℚ) < (n.minFac : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hp1Q_ge8 : (8 : ℚ) ≤ (n.minFac : ℚ) := by exact_mod_cast h8
  have hp1Q_ge1 : (1 : ℚ) ≤ (n.minFac : ℚ) := by linarith
  -- hne for H = h * (H/h)
  have hne : abundancyIndex n ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (one_le_abund _ hn_pos))
  have hH : abundancySup n =
      abundancyIndex n * (abundancySup n / abundancyIndex n) := by
    field_simp
  -- H/h = prod (1+y)
  have h_ratio_eq := ratio_eq_prod_one_add n hn0
  -- sum y < 4/p1 ≤ 1/2
  have h_sum_lt : ∑ p ∈ n.primeFactors, (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) <
      4 / (n.minFac : ℚ) := by
    have hn' : IsPrimitiveNondeficient n := ⟨⟨hn0, hsum⟩, hprim⟩
    exact sum_y_lt n hn'
  have h4_le : (4 : ℚ) / (n.minFac : ℚ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hp1Q_pos (by norm_num)]
    linarith
  have h_sum_le : ∑ p ∈ n.primeFactors, (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) ≤
      1 / 2 :=
    le_of_lt (lt_of_lt_of_le h_sum_lt h4_le)
  have h_y_nonneg : ∀ p ∈ n.primeFactors,
      0 ≤ (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have ha : 1 ≤ n.factorization p := factor_pos n p hn0 hp
    exact y_nonneg p _ hprime ha
  have h_prod_le : ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℚ) ^ (n.factorization p + 1) - 1)) ≤
      1 + 2 * ∑ p ∈ n.primeFactors, (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) :=
    prod_le_one_add_two_mul _ _ h_y_nonneg h_sum_le
  rw [← h_ratio_eq] at h_prod_le
  -- H/h < 1 + 8/p1
  have h_ratio_lt : abundancySup n / abundancyIndex n < 1 + 8 / (n.minFac : ℚ) := by
    have h1 : (1 : ℚ) + 2 * ∑ p ∈ n.primeFactors,
        (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) < 1 + 8 / (n.minFac : ℚ) := by
      have h2 : (2 : ℚ) * ∑ p ∈ n.primeFactors, (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) <
          8 / (n.minFac : ℚ) := by
        have h3 : (2 : ℚ) * ∑ p ∈ n.primeFactors,
            (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) < 2 * (4 / (n.minFac : ℚ)) :=
          mul_lt_mul_of_pos_left h_sum_lt (by norm_num)
        have h_eq : (2 : ℚ) * (4 / (n.minFac : ℚ)) = 8 / (n.minFac : ℚ) := by ring
        rw [h_eq] at h3
        exact h3
      linarith
    exact lt_of_le_of_lt h_prod_le h1
  -- h < 2 + 2/p1
  have hn' : IsPrimitiveNondeficient n := ⟨⟨hn0, hsum⟩, hprim⟩
  have h_h_lt : abundancyIndex n < 2 + 2 / (n.minFac : ℚ) := abund_lt n hn'
  have h_h_nonneg : (0 : ℚ) ≤ abundancyIndex n :=
    le_trans zero_le_one (one_le_abund _ hn_pos)
  have h_ratio_nonneg : (0 : ℚ) ≤ abundancySup n / abundancyIndex n := by
    rw [h_ratio_eq]
    apply Finset.prod_nonneg
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have ha : 1 ≤ n.factorization p := factor_pos n p hn0 hp
    have hy := y_nonneg p _ hprime ha
    linarith
  have h_pos2 : (0 : ℚ) < 2 + 2 / (n.minFac : ℚ) := by positivity
  -- H = h*(H/h) < (2+2/p1)*(1+8/p1) ≤ 2+34/p1
  rw [hH]
  have h_step1 : abundancyIndex n * (abundancySup n / abundancyIndex n) ≤
      (2 + 2 / (n.minFac : ℚ)) * (abundancySup n / abundancyIndex n) :=
    mul_le_mul_of_nonneg_right (le_of_lt h_h_lt) h_ratio_nonneg
  have h_step2 : (2 + 2 / (n.minFac : ℚ)) * (abundancySup n / abundancyIndex n) <
      (2 + 2 / (n.minFac : ℚ)) * (1 + 8 / (n.minFac : ℚ)) :=
    mul_lt_mul_of_pos_left h_ratio_lt h_pos2
  have h_prod_bound : (2 + 2 / (n.minFac : ℚ)) * (1 + 8 / (n.minFac : ℚ)) ≤
      2 + 34 / (n.minFac : ℚ) := by
    have hpos : (0 : ℚ) < (n.minFac : ℚ) := hp1Q_pos
    field_simp
    nlinarith [hp1Q_ge1]
  exact lt_of_lt_of_le (lt_of_le_of_lt h_step1 h_step2) h_prod_bound

-- Uniform bound: (H:ℝ) < 27 for all primitive n
private theorem abund_sup_lt_unif (n : ℕ) (hn : IsPrimitiveNondeficient n) :
    (abundancySup n : ℝ) < 27 := by
  have hn2 : 2 ≤ n := two_le_of_prim n hn
  obtain ⟨⟨hn0, hsum⟩, hprim⟩ := hn
  have hn_pos : 0 < n := by omega
  have hn' : IsPrimitiveNondeficient n := ⟨⟨hn0, hsum⟩, hprim⟩
  have h_h_lt3Q : abundancyIndex n < 3 := abund_lt_three n hn'
  have h_h_lt3R : (abundancyIndex n : ℝ) < 3 := by exact_mod_cast h_h_lt3Q
  have h_h_nonnegR : (0 : ℝ) ≤ (abundancyIndex n : ℝ) := by
    have h1 : (1 : ℚ) ≤ abundancyIndex n := one_le_abund _ hn_pos
    have h2 : (1 : ℝ) ≤ (abundancyIndex n : ℝ) := by exact_mod_cast h1
    linarith
  have h_sum_lt4 : ∑ p ∈ n.primeFactors, (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) <
      4 / (n.minFac : ℚ) := sum_y_lt n hn'
  have hp1Q_pos : (0 : ℚ) < (n.minFac : ℚ) := by
    have h2 := minFac_ge_two n hn2
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hp1Q_ge2 : (2 : ℚ) ≤ (n.minFac : ℚ) := by
    have h2 := minFac_ge_two n hn2
    exact_mod_cast h2
  have h4_le2 : (4 : ℚ) / (n.minFac : ℚ) ≤ 2 := by
    rw [div_le_iff₀ hp1Q_pos]
    linarith
  have h_sum_lt2Q : ∑ p ∈ n.primeFactors, (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) < 2 :=
    lt_of_lt_of_le h_sum_lt4 h4_le2
  have h_ratio_eqQ := ratio_eq_prod_one_add n hn0
  have h_ratioR_eq : ((abundancySup n / abundancyIndex n : ℚ) : ℝ) =
      ∏ p ∈ n.primeFactors, (1 + 1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1)) := by
    rw [h_ratio_eqQ, Rat.cast_prod]
    apply Finset.prod_congr rfl
    intro p _
    push_cast
    ring
  have h_each_le : ∀ p ∈ n.primeFactors,
      (1 : ℝ) + 1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1) ≤
        Real.exp (1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1)) := by
    intro p _
    have h := Real.add_one_le_exp (1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1))
    linarith
  have h_z_nonneg : ∀ p ∈ n.primeFactors,
      (0 : ℝ) ≤ 1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1) := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpr : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.one_lt
    have ha : 1 ≤ n.factorization p := factor_pos n p hn0 hp
    have hlt : (1 : ℝ) < (p : ℝ) ^ (n.factorization p + 1) := one_lt_pow₀ hpr (by omega)
    have hpos : (0 : ℝ) < (p : ℝ) ^ (n.factorization p + 1) - 1 := sub_pos.mpr hlt
    positivity
  have h_each_nonneg : ∀ p ∈ n.primeFactors,
      (0 : ℝ) ≤ (1 : ℝ) + 1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1) := by
    intro p hp
    have hz := h_z_nonneg p hp
    linarith
  have h_prod_le_exp : ∏ p ∈ n.primeFactors,
      ((1 : ℝ) + 1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1)) ≤
      ∏ p ∈ n.primeFactors, Real.exp (1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1)) :=
    Finset.prod_le_prod₀ h_each_nonneg h_each_le
  have h_prod_exp_eq : ∏ p ∈ n.primeFactors,
      Real.exp (1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1)) =
      Real.exp (∑ p ∈ n.primeFactors, 1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1)) := by
    rw [Real.exp_sum]
  have h_sumR_lt2 : (∑ p ∈ n.primeFactors, 1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1)) < 2 := by
    have h_cast_eq : (∑ p ∈ n.primeFactors, 1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1)) =
        ((∑ p ∈ n.primeFactors, (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) : ℚ) : ℝ) := by
      rw [Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro p _
      push_cast
      ring
    rw [h_cast_eq]
    exact_mod_cast h_sum_lt2Q
  have h_exp_lt : Real.exp (∑ p ∈ n.primeFactors, 1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1)) <
      Real.exp 2 := by
    apply Real.exp_lt_exp.mpr
    exact h_sumR_lt2
  have h_exp2_lt9 : Real.exp (2 : ℝ) < 9 := by
    have h1 : Real.exp (1 : ℝ) < 3 := Real.exp_one_lt_three
    have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have h_eq : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
      have : (2 : ℝ) = 1 + 1 := by norm_num
      rw [this, Real.exp_add]
    rw [h_eq]
    nlinarith [h1, hpos]
  have h_ratioR_lt9 : ((abundancySup n / abundancyIndex n : ℚ) : ℝ) < 9 := by
    rw [h_ratioR_eq]
    exact lt_of_le_of_lt (h_prod_le_exp.trans_eq h_prod_exp_eq) (lt_trans h_exp_lt h_exp2_lt9)
  have h_ratioR_nonneg : (0 : ℝ) ≤ ((abundancySup n / abundancyIndex n : ℚ) : ℝ) := by
    rw [h_ratioR_eq]
    apply Finset.prod_nonneg
    intro p hp
    exact h_each_nonneg p hp
  have hH_eq : (abundancySup n : ℝ) =
      (abundancyIndex n : ℝ) * ((abundancySup n / abundancyIndex n : ℚ) : ℝ) := by
    have hne : abundancyIndex n ≠ 0 :=
      ne_of_gt (zero_lt_one.trans_le (one_le_abund _ hn_pos))
    have hQ : abundancySup n = abundancyIndex n * (abundancySup n / abundancyIndex n) := by
      field_simp
    have hcast : ((abundancySup n : ℚ) : ℝ) =
        ((abundancyIndex n * (abundancySup n / abundancyIndex n) : ℚ) : ℝ) :=
      congrArg _ hQ
    rw [hcast]
    push_cast
    ring
  rw [hH_eq]
  have h_step1 : (abundancyIndex n : ℝ) * ((abundancySup n / abundancyIndex n : ℚ) : ℝ) ≤
      3 * ((abundancySup n / abundancyIndex n : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_right (le_of_lt h_h_lt3R) h_ratioR_nonneg
  have h_step2 : (3 : ℝ) * ((abundancySup n / abundancyIndex n : ℚ) : ℝ) < 3 * 9 :=
    mul_lt_mul_of_pos_left h_ratioR_lt9 (by norm_num)
  have h_eq : (3 : ℝ) * 9 = 27 := by norm_num
  rw [h_eq] at h_step2
  exact lt_of_le_of_lt h_step1 h_step2

/-- **Bound on $H(n)$ for primitive non-deficient numbers by the least prime factor.** For a
positive integer $n$ write $H(n) = \prod_{p \mid n} p/(p-1)$, the product over the prime
divisors of $n$. There is a real constant $C$ such that every primitive non-deficient number
$n$ with least prime factor $p_1$ satisfies $H(n) \le 2 + C/p_1$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 8 (`integers-2025-A59-prop-8`). -/
public theorem exists_abundancySup_le_two_add_div_minFac :
    ∃ C : ℝ, ∀ n : ℕ, IsPrimitiveNondeficient n →
      (abundancySup n : ℝ) ≤ 2 + C / n.minFac := by
  use 200
  intro n hn
  have hn2 : 2 ≤ n := two_le_of_prim n hn
  have hp1_ge2 : 2 ≤ n.minFac := minFac_ge_two n hn2
  by_cases h8 : 8 ≤ n.minFac
  · -- Large case: H < 2+34/p1 in ℚ, so ≤ 2+200/p1 in ℝ
    have hQ : abundancySup n < 2 + 34 / (n.minFac : ℚ) := abund_sup_lt_large n hn h8
    have hp1Q_pos : (0 : ℚ) < (n.minFac : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have h_le_Q : (2 : ℚ) + 34 / (n.minFac : ℚ) ≤ 2 + 200 / (n.minFac : ℚ) := by
      have h1 : (34 : ℚ) / (n.minFac : ℚ) ≤ 200 / (n.minFac : ℚ) := by
        have hpos := hp1Q_pos
        field_simp
        norm_num
      linarith
    have h_lt_Q : abundancySup n < 2 + 200 / (n.minFac : ℚ) := lt_of_lt_of_le hQ h_le_Q
    have h_cast_lt : ((abundancySup n : ℚ) : ℝ) < ((2 + 200 / (n.minFac : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast h_lt_Q
    have h_cast_eq : ((2 + 200 / (n.minFac : ℚ) : ℚ) : ℝ) = 2 + 200 / (n.minFac : ℝ) := by
      push_cast
      ring
    rw [h_cast_eq] at h_cast_lt
    exact le_of_lt h_cast_lt
  · -- Small case: H < 27 ≤ 2+200/p1
    have h8lt : n.minFac < 8 := by omega
    have h_unif : (abundancySup n : ℝ) < 27 := abund_sup_lt_unif n hn
    have hmin_le7 : n.minFac ≤ 7 := by omega
    have hR_pos : (0 : ℝ) < (n.minFac : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hR_le7 : (n.minFac : ℝ) ≤ 7 := by exact_mod_cast hmin_le7
    have h25 : (25 : ℝ) ≤ 200 / (n.minFac : ℝ) := by
      rw [le_div_iff₀ hR_pos]
      nlinarith [hR_le7]
    have h27 : (27 : ℝ) ≤ 2 + 200 / (n.minFac : ℝ) := by linarith
    exact le_of_lt (lt_of_lt_of_le h_unif h27)

section OddPart

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

private theorem prod_sub_one_lt_prod_of_nonempty (s : Finset ℕ) :
    (∀ p ∈ s, 2 ≤ p) → s.Nonempty → ∏ p ∈ s, (p - 1) < ∏ p ∈ s, p := fun h2 hne =>
  Finset.prod_lt_prod_of_nonempty₀ (fun p hp => by have := h2 p hp; omega)
    (fun p hp => by have := h2 p hp; omega) hne

private theorem prod_primeFactors_le_self (m : ℕ) (hm : m ≠ 0) :
    ∏ p ∈ m.primeFactors, p ≤ m :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)

private theorem prime_not_dvd_ordCompl_succ_self (q : ℕ) (hq : q.Prime) :
    ¬ q ∣ ordCompl[2] (q + 1) := by
  intro hdvd
  have h1 : q ∣ q + 1 := hdvd.trans (Nat.ordCompl_dvd (q + 1) 2)
  have h2 : q ∣ 1 := by
    have hsub := Nat.dvd_sub h1 (dvd_refl q)
    simpa using hsub
  exact hq.ne_one (Nat.dvd_one.mp h2)

/-- **No odd prime $q$ lifts $H$ of the odd part of $q + 1$ across $2$.** For a positive integer
$m$ write $H(m) = \prod_{p \mid m} p/(p-1)$, the product over the prime divisors of $m$, and
$\operatorname{odd}(m)$ for the largest odd divisor of $m$. There is no odd prime $q$ with
$H(\operatorname{odd}(q+1)) < 2$ and $H(q \cdot \operatorname{odd}(q+1)) > 2$.

For $q = 2$ the conclusion fails: $H(3) = 3/2 < 2$ and $H(6) = 3 > 2$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 10, corrected to odd primes (`integers-2025-A59-prop-10`). -/
public theorem not_abundancySup_oddPart_succ_lt_two_and_two_lt
    (q : ℕ) (hq : q.Prime) (hodd : Odd q) :
    ¬ (abundancySup (ordCompl[2] (q + 1)) < 2 ∧
      2 < abundancySup (q * ordCompl[2] (q + 1))) := by
  rintro ⟨hlt, hgt⟩
  have hq1_ne : q + 1 ≠ 0 := by omega
  have hm_pos : 0 < ordCompl[2] (q + 1) := Nat.ordCompl_pos 2 hq1_ne
  have hm_ne : ordCompl[2] (q + 1) ≠ 0 := hm_pos.ne'
  have hqdvd : ¬ q ∣ ordCompl[2] (q + 1) := prime_not_dvd_ordCompl_succ_self q hq
  have h2dvd : ¬ 2 ∣ ordCompl[2] (q + 1) := Nat.not_dvd_ordCompl Nat.prime_two hq1_ne
  have hodd_s : ∀ p ∈ (ordCompl[2] (q + 1)).primeFactors, p.Prime ∧ Odd p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    refine ⟨hpp, hpp.odd_of_ne_two ?_⟩
    rintro rfl
    exact h2dvd (Nat.dvd_of_mem_primeFactors hp)
  have hqmem : q ∉ (ordCompl[2] (q + 1)).primeFactors := by
    intro hmem
    exact hqdvd (Nat.mem_primeFactors.mp hmem).2.1
  have hqs : (q * ordCompl[2] (q + 1)).primeFactors =
      insert q (ordCompl[2] (q + 1)).primeFactors := by
    rw [Nat.primeFactors_mul hq.ne_zero hm_ne, hq.primeFactors,
      Finset.singleton_union]
  have hH : abundancySup (q * ordCompl[2] (q + 1)) =
      abundancySup (ordCompl[2] (q + 1)) * ((q : ℚ) / ((q : ℚ) - 1)) := by
    change (∏ p ∈ (q * ordCompl[2] (q + 1)).primeFactors, (p : ℚ) / ((p : ℚ) - 1)) =
      (∏ p ∈ (ordCompl[2] (q + 1)).primeFactors, (p : ℚ) / ((p : ℚ) - 1)) *
        ((q : ℚ) / ((q : ℚ) - 1))
    rw [hqs, Finset.prod_insert hqmem, mul_comm]
  have hle2 :
      (∏ p ∈ (ordCompl[2] (q + 1)).primeFactors, (p : ℚ) / ((p : ℚ) - 1)) ≤ 2 :=
    hlt.le
  have hgt2 : 2 <
      (∏ p ∈ (ordCompl[2] (q + 1)).primeFactors, (p : ℚ) / ((p : ℚ) - 1)) *
        ((q : ℚ) / ((q : ℚ) - 1)) := by
    change 2 < abundancySup (ordCompl[2] (q + 1)) * ((q : ℚ) / ((q : ℚ) - 1))
    rw [← hH]
    exact hgt
  have hbound := le_two_mul_prod_sub_one_sub_one_of_two_lt
    _ hodd_s hle2 q hq hodd hgt2
  have hP1 : 1 ≤ ∏ p ∈ (ordCompl[2] (q + 1)).primeFactors, (p - 1) := by
    have hpos : 0 < ∏ p ∈ (ordCompl[2] (q + 1)).primeFactors, (p - 1) :=
      Finset.prod_pos (fun p hp =>
        Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt)
    omega
  have hq1 : q + 1 ≤ 2 * ∏ p ∈ (ordCompl[2] (q + 1)).primeFactors, (p - 1) := by
    omega
  have hfac : ordCompl[2] (q + 1) * 2 ^ (q + 1).factorization 2 = q + 1 :=
    (Nat.mul_comm _ _).trans (Nat.ordProj_mul_ordCompl_eq_self (q + 1) 2)
  have h2ddvd : 2 ∣ q + 1 := even_iff_two_dvd.mp hodd.add_one
  have ha : 1 ≤ (q + 1).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two hq1_ne h2ddvd
  obtain ⟨b, hb⟩ : ∃ b, (q + 1).factorization 2 = b + 1 :=
    ⟨_, (Nat.sub_add_cancel ha).symm⟩
  have hle : ordCompl[2] (q + 1) * (2 ^ b * 2) ≤
      2 * ∏ p ∈ (ordCompl[2] (q + 1)).primeFactors, (p - 1) := by
    have h2a : 2 ^ (q + 1).factorization 2 = 2 ^ b * 2 := by
      rw [hb, pow_succ]
    rw [← h2a, hfac]
    exact hq1
  have hstep : ordCompl[2] (q + 1) * 2 ^ b ≤
      ∏ p ∈ (ordCompl[2] (q + 1)).primeFactors, (p - 1) := by
    have h'' : 2 * (ordCompl[2] (q + 1) * 2 ^ b) ≤
        2 * ∏ p ∈ (ordCompl[2] (q + 1)).primeFactors, (p - 1) := by
      have heq : 2 * (ordCompl[2] (q + 1) * 2 ^ b) =
          ordCompl[2] (q + 1) * (2 ^ b * 2) := by ac_rfl
      rw [heq]
      exact hle
    exact le_of_mul_le_mul_left h'' (by omega)
  have hm1le : ordCompl[2] (q + 1) ≤ ordCompl[2] (q + 1) * 2 ^ b :=
    calc ordCompl[2] (q + 1) = ordCompl[2] (q + 1) * 1 := (mul_one _).symm
      _ ≤ ordCompl[2] (q + 1) * 2 ^ b :=
        Nat.mul_le_mul_left _ (one_le_pow₀ (by omega : (1 : ℕ) ≤ 2))
  by_cases hm1 : ordCompl[2] (q + 1) = 1
  · have hP : ∏ p ∈ (ordCompl[2] (q + 1)).primeFactors, (p - 1) = 1 := by
      rw [hm1, Nat.primeFactors_one, Finset.prod_empty]
    have hq2 := hq.two_le
    omega
  · have hsne : (ordCompl[2] (q + 1)).primeFactors.Nonempty := by
      obtain ⟨p, hpp, hdvd⟩ := Nat.exists_prime_and_dvd hm1
      exact ⟨p, Nat.mem_primeFactors.mpr ⟨hpp, hdvd, hm_ne⟩⟩
    have hstrict := prod_sub_one_lt_prod_of_nonempty _
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le) hsne
    have hrad := prod_primeFactors_le_self _ hm_ne
    have hcontra : ordCompl[2] (q + 1) < ordCompl[2] (q + 1) :=
      lt_of_le_of_lt (hm1le.trans hstep) (lt_of_lt_of_le hstrict hrad)
    exact absurd hcontra (lt_irrefl _)

end OddPart

end MetaMathlibExt
