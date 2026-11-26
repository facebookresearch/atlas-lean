/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
public import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficient
public import MathlibExt.NumberTheory.EulerPrime
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeProduct

/-!
# Two propositions of Zelinsky on the prime divisors of odd perfect numbers

## Main statements

* `not_abundancySup_oddPart_succ_lt_two_and_two_lt`: there is no odd prime `q` with
  `H(odd(q+1)) < 2` and `H(q * odd(q+1)) > 2`, where `H` is `abundancySup` and `odd` is the largest
  odd divisor. The proof combines the prime bound `le_two_mul_prod_sub_one_sub_one_of_two_lt` with
  the factorization `q + 1 = 2 ^ a * m`.
* `eulerianForm_exponent_eq_one_or_pow_five_lt`: if `(n, q, e, m)` is in Eulerian form then `e = 1`
  or `q ^ 5 < 2 * m ^ 2`.

## References

* Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd Perfect or Odd
  Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59, Propositions 10 and 11.
-/

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

section OddPart

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

private theorem prod_sub_one_lt_prod_of_nonempty (s : Finset ℕ) :
    (∀ p ∈ s, 2 ≤ p) → s.Nonempty → ∏ p ∈ s, (p - 1) < ∏ p ∈ s, p := by
  induction s using Finset.induction with
  | empty =>
    intro _ hne
    obtain ⟨x, hx⟩ := hne
    simp at hx
  | insert a t hat ih =>
    intro h2 _
    rw [Finset.prod_insert hat, Finset.prod_insert hat]
    have ha2 : 2 ≤ a := h2 a (Finset.mem_insert_self a t)
    by_cases ht : t.Nonempty
    · have hlt := ih (fun p hp => h2 p (Finset.mem_insert_of_mem hp)) ht
      have hTpos : 0 < ∏ p ∈ t, p :=
        Finset.prod_pos (fun p hp => by
          have hp2 := h2 p (Finset.mem_insert_of_mem hp)
          omega)
      have hsub_pos : 0 < a - 1 := by omega
      have hsub_lt : a - 1 < a := by omega
      calc (a - 1) * ∏ p ∈ t, (p - 1) < (a - 1) * ∏ p ∈ t, p :=
            mul_lt_mul_of_pos_left hlt hsub_pos
        _ < a * ∏ p ∈ t, p := mul_lt_mul_of_pos_right hsub_lt hTpos
    · rw [Finset.not_nonempty_iff_eq_empty.mp ht, Finset.prod_empty,
        Finset.prod_empty, mul_one, mul_one]
      omega

private theorem prod_primeFactors_le_self (m : ℕ) (hm : m ≠ 0) :
    ∏ p ∈ m.primeFactors, p ≤ m := by
  have hdiv : ∏ p ∈ m.primeFactors, p ∣ m := by
    have h := Finset.prod_dvd_prod_of_dvd (fun p => p)
      (fun p => p ^ m.factorization p) (fun p hp => by
        change p ∣ p ^ m.factorization p
        have hpos := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hm
          (Nat.dvd_of_mem_primeFactors hp)
        calc p = p ^ 1 := (pow_one p).symm
          _ ∣ p ^ m.factorization p := pow_dvd_pow p hpos)
    rwa [← Nat.prod_primeFactors_pow_factorization hm] at h
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdiv

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
Proposition 10 (`integers-2025-A59-prop-10`). -/
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
