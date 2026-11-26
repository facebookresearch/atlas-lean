/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
public import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficient
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.PrimeFin
import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeProduct

/-!
# No odd prime lifts the odd-part prime product across two

The main result is `not_abundancySup_oddPart_succ_lt_two_and_two_lt`: there is no odd
prime `q` with `H(odd(q+1)) < 2` and `H(q * odd(q+1)) > 2`, where `H` is
`abundancySup` and `odd` is the largest odd divisor. The proof combines the prime bound
`le_two_mul_prod_sub_one_sub_one_of_two_lt` with the factorization `q + 1 = 2 ^ a * m`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 10.
-/

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

namespace MetaMathlibExt

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

end MetaMathlibExt
