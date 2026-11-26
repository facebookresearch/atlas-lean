/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficient
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.ArithmeticFunction.AbundancySupDivIndex
import MathlibExt.NumberTheory.EulerPrime

/-! # Prime product bound for odd perfect numbers

This file proves Zelinsky's upper bound on `H(n) = ∏_{p ∣ n} p/(p-1)` for an odd
perfect number `n` in terms of its least prime factor `n.minFac`.

Statement source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime
Divisors of an Odd Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025),
Article A59 (arXiv:2402.14234v5). The paper writes `H(n) = ∏_{p ∣ n} p/(p-1)` for
`abundancySup` and `p₁` for `n.minFac`.
-/

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

namespace MetaMathlibExt

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

end MetaMathlibExt
