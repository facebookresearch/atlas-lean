/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.FieldSimp
import MathlibExt.NumberTheory.SumSquaredDivisorsProduct
public import MathlibExt.NumberTheory.SZumkeller

/-!
# Even s-Zumkeller numbers have at least twelve divisors

The theorem `twelve_le_card_divisors_of_isSZumkeller` states that an even
s-Zumkeller number has at least twelve positive divisors.

Statements from Jayanta Kalita and Helen K. Saikia, "A Study on Generalized
Zumkeller Numbers", *INTEGERS* 24 (2024), Article A95.
-/

namespace MetaMathlibExt

private theorem subset_two_three_of_isSZumkeller_even (n : ℕ) (he : Even n) (h3 : 3 ∣ n)
    (hn : n ≠ 0) : ({2, 3} : Finset ℕ) ⊆ n.primeFactors := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact Nat.Prime.mem_primeFactors (by decide) he.two_dvd hn
  · exact Nat.Prime.mem_primeFactors (by decide) h3 hn

private theorem sigma_div_sq_lower_of_isSZumkeller_even (n : ℕ) (h : IsSZumkeller n)
    (he : Even n) (hn : 0 < n) :
    (3 : ℚ) / 2 ≤ (ArithmeticFunction.sigma 2 n : ℚ) / (n : ℚ) ^ 2 := by
  obtain ⟨S, _, hS⟩ := (isSZumkeller_iff_of_even n hn he).mp h
  have hnonneg : 0 ≤ ∑ d ∈ S, (d : ℤ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hle : 3 * (n : ℚ) ^ 2 ≤ 2 * (ArithmeticFunction.sigma 2 n : ℚ) := by
    exact_mod_cast (show 3 * (n : ℤ) ^ 2 ≤ 2 * ArithmeticFunction.sigma 2 n by omega)
  have hpos : (0 : ℚ) < (n : ℚ) ^ 2 := by
    have hn' : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
    positivity
  rw [le_div_iff₀ hpos]
  linarith

private theorem three_le_card_primeFactors_of_isSZumkeller_even_aux (n : ℕ)
    (h : IsSZumkeller n) (he : Even n) (hn1 : 1 < n) : 3 ≤ n.primeFactors.card := by
  by_contra hc
  push Not at hc
  have hn : n ≠ 0 := by omega
  have hsub : ({2, 3} : Finset ℕ) ⊆ n.primeFactors :=
    subset_two_three_of_isSZumkeller_even n he (three_dvd_of_isSZumkeller n h he) hn
  have hcard2 : ({2, 3} : Finset ℕ).card = 2 := by decide
  have h2le : 2 ≤ n.primeFactors.card := by
    rw [← hcard2]
    exact Finset.card_le_card hsub
  have hcard : n.primeFactors.card = 2 := by omega
  have heq : ({2, 3} : Finset ℕ) = n.primeFactors :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; decide)
  have hlower := sigma_div_sq_lower_of_isSZumkeller_even n h he (by omega)
  have hupper := (sigma_two_prod_formulas n hn).2.2 hn1
  rw [← heq] at hupper
  have h23 : ∏ p ∈ ({2, 3} : Finset ℕ), ((p : ℚ) ^ 2 / (p ^ 2 - 1)) = 3 / 2 := by
    rw [Finset.prod_insert (by decide : (2 : ℕ) ∉ ({3} : Finset ℕ)),
      Finset.prod_singleton]
    norm_num
  rw [h23] at hupper
  linarith

/-- **Even s-Zumkeller numbers have at least twelve divisors.** If $n$ is an even s-Zumkeller
number, then $n$ has at least $12$ positive divisors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 3. -/
public theorem twelve_le_card_divisors_of_isSZumkeller (n : ℕ) (h : IsSZumkeller n)
    (he : Even n) : 12 ≤ n.divisors.card := by
  by_contra hc
  push Not at hc
  have hcopy := h
  obtain ⟨A, hA, hne, -, -⟩ := h
  have hn1 : 1 < n := Nat.nonempty_properDivisors.mp (hne.mono hA)
  have hn : n ≠ 0 := by omega
  have h3 : 3 ∣ n := three_dvd_of_isSZumkeller n hcopy he
  have hlower := sigma_div_sq_lower_of_isSZumkeller_even n hcopy he (by omega)
  have hcard3 :=
    three_le_card_primeFactors_of_isSZumkeller_even_aux n hcopy he hn1
  have h2pow : 2 ^ n.primeFactors.card ≤ n.divisors.card := by
    calc 2 ^ n.primeFactors.card = ∏ x ∈ n.primeFactors, 2 := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ n.primeFactors, (n.factorization p + 1) := by
      apply Finset.prod_le_prod
      intro p hp
      have hpos := Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp)
        hn (Nat.dvd_of_mem_primeFactors hp)
      omega
    _ = n.divisors.card := (Nat.card_divisors hn).symm
  have hcard3eq : n.primeFactors.card = 3 := by
    by_contra hne3
    have h4 : 4 ≤ n.primeFactors.card := by omega
    have h16 : 16 ≤ 2 ^ n.primeFactors.card := by
      calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n.primeFactors.card := pow_le_pow_right₀ (by norm_num) h4
    omega
  have hexp1 : ∀ p ∈ n.primeFactors, n.factorization p = 1 := by
    intro p hp
    have hpos := Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp)
      hn (Nat.dvd_of_mem_primeFactors hp)
    by_contra hne1
    have h2 : 2 ≤ n.factorization p := by omega
    have hsplit : ∏ q ∈ n.primeFactors, (n.factorization q + 1)
        = (n.factorization p + 1) * ∏ q ∈ n.primeFactors.erase p,
          (n.factorization q + 1) := (Finset.mul_prod_erase _ _ hp).symm
    have hrest : 2 ^ (n.primeFactors.erase p).card
        ≤ ∏ q ∈ n.primeFactors.erase p, (n.factorization q + 1) := by
      have hconst : ∏ x ∈ n.primeFactors.erase p, 2
          = 2 ^ (n.primeFactors.erase p).card := Finset.prod_const 2
      rw [← hconst]
      apply Finset.prod_le_prod
      intro q hq
      have hqS := Finset.mem_of_mem_erase hq
      have hqpos := Nat.Prime.factorization_pos_of_dvd
        (Nat.prime_of_mem_primeFactors hqS) hn (Nat.dvd_of_mem_primeFactors hqS)
      omega
    have hcardE : (n.primeFactors.erase p).card = 2 := by
      rw [Finset.card_erase_of_mem hp, hcard3eq]
    have h3le : 3 ≤ n.factorization p + 1 := by omega
    rw [hcardE] at hrest
    have h4le : 4 ≤ ∏ q ∈ n.primeFactors.erase p, (n.factorization q + 1) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ ∏ q ∈ n.primeFactors.erase p, (n.factorization q + 1) := hrest
    have h12 : 12 ≤ n.divisors.card := by
      rw [Nat.card_divisors hn, hsplit]
      calc (12 : ℕ) = 3 * 4 := by norm_num
      _ ≤ 3 * ∏ q ∈ n.primeFactors.erase p, (n.factorization q + 1) :=
        mul_le_mul_right h4le 3
      _ ≤ (n.factorization p + 1) * ∏ q ∈ n.primeFactors.erase p,
          (n.factorization q + 1) := mul_le_mul_left h3le _
    omega
  have hsub : ({2, 3} : Finset ℕ) ⊆ n.primeFactors :=
    subset_two_three_of_isSZumkeller_even n he h3 hn
  have hrest1 : (n.primeFactors \ {2, 3}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hcard3eq]
    decide
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hrest1
  have hqmem : q ∈ n.primeFactors \ {2, 3} := by
    rw [hq]
    exact Finset.mem_singleton_self q
  have hqS : q ∈ n.primeFactors := (Finset.mem_sdiff.mp hqmem).1
  have hq23 : q ≠ 2 ∧ q ≠ 3 := by
    have hqnotin := (Finset.mem_sdiff.mp hqmem).2
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hqnotin
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqS
  have hq5 : 5 ≤ q := hqprime.five_le_of_ne_two_of_ne_three hq23.1 hq23.2
  have hNorm := (sigma_two_prod_formulas n hn).2.1
  have hNorm2 : (ArithmeticFunction.sigma 2 n : ℚ) / (n : ℚ) ^ 2
      = ∏ p ∈ n.primeFactors, (((p : ℚ) ^ 2 + 1) / (p : ℚ) ^ 2) := by
    rw [hNorm]
    apply Finset.prod_congr rfl
    intro p hp
    rw [hexp1 p hp]
    change ((p : ℚ) ^ 4 - 1) / ((p : ℚ) ^ 2 * ((p : ℚ) ^ 2 - 1))
      = ((p : ℚ) ^ 2 + 1) / (p : ℚ) ^ 2
    have hp0 : (p : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    have h4 : (4 : ℚ) ≤ (p : ℚ) ^ 2 := by
      have h2 : (2 : ℚ) ≤ (p : ℚ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      nlinarith [sq_nonneg ((p : ℚ) - 2)]
    have hne : (p : ℚ) ^ 2 - 1 ≠ 0 := by
      have hpos : (0 : ℚ) < (p : ℚ) ^ 2 - 1 := by linarith
      exact ne_of_gt hpos
    have hp2 : (p : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hp0
    have hmul : (p : ℚ) ^ 2 * ((p : ℚ) ^ 2 - 1) ≠ 0 := mul_ne_zero hp2 hne
    field_simp
    ring
  have hsplit2 := Finset.prod_sdiff (s₁ := ({2, 3} : Finset ℕ)) (s₂ := n.primeFactors)
    (f := fun p : ℕ => (((p : ℚ) ^ 2 + 1) / (p : ℚ) ^ 2)) hsub
  rw [hq, Finset.prod_singleton] at hsplit2
  have h23' : ∏ p ∈ ({2, 3} : Finset ℕ), (((p : ℚ) ^ 2 + 1) / (p : ℚ) ^ 2) = 25 / 18 := by
    rw [Finset.prod_insert (by decide : (2 : ℕ) ∉ ({3} : Finset ℕ)),
      Finset.prod_singleton]
    norm_num
  rw [h23'] at hsplit2
  have hsplit2b : (((q : ℚ) ^ 2 + 1) / (q : ℚ) ^ 2) * (25 / 18)
      = ∏ p ∈ n.primeFactors, (((p : ℚ) ^ 2 + 1) / (p : ℚ) ^ 2) := hsplit2
  rw [← hsplit2b] at hNorm2
  have hq2 : (25 : ℚ) ≤ (q : ℚ) ^ 2 := by
    have h5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq5
    nlinarith [sq_nonneg ((q : ℚ) - 5)]
  have hqpos : (0 : ℚ) < (q : ℚ) ^ 2 := lt_of_lt_of_le (by norm_num) hq2
  have hfinal : (((q : ℚ) ^ 2 + 1) / (q : ℚ) ^ 2) * (25 / 18) < 3 / 2 := by
    rw [div_mul_div_comm, div_lt_iff₀ (mul_pos hqpos (by norm_num))]
    linarith [hq2]
  linarith

end MetaMathlibExt
