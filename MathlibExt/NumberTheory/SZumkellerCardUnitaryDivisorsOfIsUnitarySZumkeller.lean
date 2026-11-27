/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SZumkeller
import MathlibExt.NumberTheory.SZumkellerIsUnitarySZumkellerBounds
import MathlibExt.NumberTheory.UnitaryDivisorCount
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Unitary divisor counts of unitary s-Zumkeller numbers

The least unitary divisor exceeding one determines lower bounds for the number
of unitary divisors of a unitary s-Zumkeller number.

Statements from Jayanta Kalita and Helen K. Saikia, "A Study on Generalized
Zumkeller Numbers", *INTEGERS* 24 (2024), Article A95, Proposition 12.
-/

namespace MetaMathlibExt

@[expose] public section

/-- A unitary s-Zumkeller number is nonzero. -/
private theorem ne_zero_of_isUnitarySZumkeller {n : ℕ} (h : IsUnitarySZumkeller n) :
    n ≠ 0 := by
  rintro rfl
  obtain ⟨A, hA, hne, _, _⟩ := h
  rw [Nat.unitaryDivisors_zero, Finset.erase_empty] at hA
  obtain ⟨x, hx⟩ := hne
  exact Finset.notMem_empty x (hA hx)

/-- Every nonzero number is its own unitary divisor. -/
private theorem self_mem_unitaryDivisors {n : ℕ} (hn : n ≠ 0) :
    n ∈ Nat.unitaryDivisors n := by
  rw [Nat.mem_unitaryDivisors]
  refine ⟨dvd_refl n, hn, ?_⟩
  rw [Nat.div_self (Nat.pos_of_ne_zero hn)]
  exact Nat.coprime_one_right n

/-- One is a unitary divisor of every nonzero number. -/
private theorem one_mem_unitaryDivisors {n : ℕ} (hn : n ≠ 0) :
    1 ∈ Nat.unitaryDivisors n := by
  rw [Nat.mem_unitaryDivisors]
  refine ⟨one_dvd n, hn, ?_⟩
  rw [Nat.div_one]
  exact Nat.coprime_one_left n

/-- The first small primes, by index; anything beyond index five is seventeen. -/
private def smallPrime : ℕ → ℕ
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 11
  | 5 => 13
  | _ => 17

/-- No square equals eight, ten, fifteen or seventeen. -/
private theorem not_sq_mem {x v : ℕ} (h : x ^ 2 = v)
    (hv : v = 8 ∨ v = 10 ∨ v = 15 ∨ v = 17) : False := by
  have hx4 : x ≤ 4 := by
    by_contra hc
    have hc5 : 5 ≤ x := by omega
    have h25 : 25 ≤ x ^ 2 :=
      calc (25 : ℕ) = 5 ^ 2 := by norm_num
        _ ≤ x ^ 2 := Nat.pow_le_pow_left hc5 2
    omega
  have hx0 : 0 ≤ x := Nat.zero_le x
  interval_cases x <;> norm_num at h <;> omega

/-- A product over at most six primes is maximized at the smallest primes. -/
private theorem prod_le_smallPrimes_prod (m : ℕ) : m ≤ 6 → ∀ (S : Finset ℕ),
    (∀ p ∈ S, p.Prime) → S.card = m →
    ∏ p ∈ S, (1 + 1 / (p : ℚ) ^ 2) ≤
      ∏ j ∈ Finset.range m, (1 + 1 / (smallPrime j : ℚ) ^ 2) := by
  induction m with
  | zero =>
    intro _ S _ hcard
    have hSe : S = ∅ := Finset.card_eq_zero.mp (by omega)
    simp [hSe]
  | succ m ih =>
    intro hm6 S hS hcard
    have hne : S.Nonempty := by
      rw [← Finset.card_pos, hcard]
      omega
    set s := S.max' hne
    have hsS : s ∈ S := Finset.max'_mem S hne
    have hsP : s.Prime := hS s hsS
    have hS'card : (S.erase s).card = m := by
      rw [Finset.card_erase_of_mem hsS, hcard]
      omega
    have hS' : ∀ p ∈ S.erase s, p.Prime := fun p hp => hS p (Finset.mem_of_mem_erase hp)
    have hm6' : m ≤ 6 := by omega
    have ih' := ih hm6' (S.erase s) hS' hS'card
    have hs_ge : smallPrime m ≤ s := by
      by_contra hcon
      have hcon' : s < smallPrime m := by omega
      have hm5 : m ≤ 5 := by omega
      have hm0 : 0 ≤ m := Nat.zero_le m
      interval_cases m
      · have e0 : smallPrime 0 = 2 := rfl
        have hf0 : ∀ p : ℕ, p < 2 → p.Prime → p ∈ (∅ : Finset ℕ) := by decide
        rw [e0] at hcon'
        have hsub : S ⊆ ∅ := by
          intro p hpS
          have hple : p ≤ s := Finset.le_max' S p hpS
          have hplt : p < 2 := lt_of_le_of_lt hple hcon'
          exact hf0 p hplt (hS p hpS)
        have hcle := Finset.card_le_card hsub
        rw [hcard] at hcle
        simp at hcle
      · have e1 : smallPrime 1 = 3 := rfl
        have hf1 : ∀ p : ℕ, p < 3 → p.Prime → p ∈ ({2} : Finset ℕ) := by decide
        have c1 : ({2} : Finset ℕ).card = 1 := by decide
        rw [e1] at hcon'
        have hsub : S ⊆ {2} := by
          intro p hpS
          have hple : p ≤ s := Finset.le_max' S p hpS
          have hplt : p < 3 := lt_of_le_of_lt hple hcon'
          exact hf1 p hplt (hS p hpS)
        have hcle := Finset.card_le_card hsub
        rw [hcard, c1] at hcle
        norm_num at hcle
      · have e2 : smallPrime 2 = 5 := rfl
        have hf2 : ∀ p : ℕ, p < 5 → p.Prime → p ∈ ({2, 3} : Finset ℕ) := by decide
        have c2 : ({2, 3} : Finset ℕ).card = 2 := by decide
        rw [e2] at hcon'
        have hsub : S ⊆ {2, 3} := by
          intro p hpS
          have hple : p ≤ s := Finset.le_max' S p hpS
          have hplt : p < 5 := lt_of_le_of_lt hple hcon'
          exact hf2 p hplt (hS p hpS)
        have hcle := Finset.card_le_card hsub
        rw [hcard, c2] at hcle
        norm_num at hcle
      · have e3 : smallPrime 3 = 7 := rfl
        have hf3 : ∀ p : ℕ, p < 7 → p.Prime → p ∈ ({2, 3, 5} : Finset ℕ) := by decide
        have c3 : ({2, 3, 5} : Finset ℕ).card = 3 := by decide
        rw [e3] at hcon'
        have hsub : S ⊆ {2, 3, 5} := by
          intro p hpS
          have hple : p ≤ s := Finset.le_max' S p hpS
          have hplt : p < 7 := lt_of_le_of_lt hple hcon'
          exact hf3 p hplt (hS p hpS)
        have hcle := Finset.card_le_card hsub
        rw [hcard, c3] at hcle
        norm_num at hcle
      · have e4 : smallPrime 4 = 11 := rfl
        have hf4 : ∀ p : ℕ, p < 11 → p.Prime → p ∈ ({2, 3, 5, 7} : Finset ℕ) := by decide
        have c4 : ({2, 3, 5, 7} : Finset ℕ).card = 4 := by decide
        rw [e4] at hcon'
        have hsub : S ⊆ {2, 3, 5, 7} := by
          intro p hpS
          have hple : p ≤ s := Finset.le_max' S p hpS
          have hplt : p < 11 := lt_of_le_of_lt hple hcon'
          exact hf4 p hplt (hS p hpS)
        have hcle := Finset.card_le_card hsub
        rw [hcard, c4] at hcle
        norm_num at hcle
      · have e5 : smallPrime 5 = 13 := rfl
        have hf5 : ∀ p : ℕ, p < 13 → p.Prime → p ∈ ({2, 3, 5, 7, 11} : Finset ℕ) := by decide
        have c5 : ({2, 3, 5, 7, 11} : Finset ℕ).card = 5 := by decide
        rw [e5] at hcon'
        have hsub : S ⊆ {2, 3, 5, 7, 11} := by
          intro p hpS
          have hple : p ≤ s := Finset.le_max' S p hpS
          have hplt : p < 13 := lt_of_le_of_lt hple hcon'
          exact hf5 p hplt (hS p hpS)
        have hcle := Finset.card_le_card hsub
        rw [hcard, c5] at hcle
        norm_num at hcle
    have hsmall2 : 2 ≤ smallPrime m := by
      unfold smallPrime
      split <;> omega
    have hfle : (1 : ℚ) + 1 / (s : ℚ) ^ 2 ≤ 1 + 1 / (smallPrime m : ℚ) ^ 2 := by
      have hb0 : (0 : ℚ) < smallPrime m := by
        exact_mod_cast lt_of_lt_of_le (by norm_num) hsmall2
      have hle : (smallPrime m : ℚ) ^ 2 ≤ (s : ℚ) ^ 2 := by
        have hab : (smallPrime m : ℚ) ≤ (s : ℚ) := by exact_mod_cast hs_ge
        have ha0 : (0 : ℚ) ≤ (smallPrime m : ℚ) := by positivity
        exact pow_le_pow_left₀ ha0 hab 2
      have hpos : (0 : ℚ) < (smallPrime m : ℚ) ^ 2 := pow_pos hb0 2
      have hdiv := one_div_le_one_div_of_le hpos hle
      linarith
    have hprod_eq : ∏ p ∈ S, (1 + 1 / (p : ℚ) ^ 2)
        = (∏ p ∈ S.erase s, (1 + 1 / (p : ℚ) ^ 2)) * (1 + 1 / (s : ℚ) ^ 2) :=
      (Finset.mul_prod_erase S _ hsS).symm.trans (mul_comm _ _)
    have hprod_range : ∏ j ∈ Finset.range (m + 1), (1 + 1 / (smallPrime j : ℚ) ^ 2)
        = (∏ j ∈ Finset.range m, (1 + 1 / (smallPrime j : ℚ) ^ 2)) *
          (1 + 1 / (smallPrime m : ℚ) ^ 2) :=
      Finset.prod_range_succ _ _
    rw [hprod_eq, hprod_range]
    apply mul_le_mul ih' hfle _ _
    · positivity
    · apply Finset.prod_nonneg
      intro j _
      positivity

/-- A split with a singleton side over three explicit elements is impossible. -/
private theorem nosplit_of_singleton {q x : ℕ} {E B : Finset ℕ}
    (hBsub : B ⊆ E) (hB1 : B.card = 1)
    (hsum : ∑ d ∈ B, d ^ 2 = ∑ d ∈ E \ B, d ^ 2)
    (hEeq : E = {1, q, x}) (h1q : (1 : ℕ) ≠ q) (hx1 : x ≠ 1) (hxq : x ≠ q)
    (h3 : 3 ≤ q) (h4 : q ≤ 4) : False := by
  obtain ⟨y, hyB⟩ := Finset.card_eq_one.mp hB1
  have h1mem : (1 : ℕ) ∉ ({q, x} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact not_or.mpr ⟨h1q, Ne.symm hx1⟩
  have hqmem : q ∉ ({x} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    exact Ne.symm hxq
  have hsumE : ∑ d ∈ E, d ^ 2 = 1 + q ^ 2 + x ^ 2 := by
    rw [hEeq, Finset.sum_insert h1mem, Finset.sum_insert hqmem, Finset.sum_singleton]
    ring
  have hsplit := Finset.sum_sdiff (f := fun d : ℕ => d ^ 2) hBsub
  rw [hyB, Finset.sum_singleton] at hsum hsplit
  have heq : 2 * y ^ 2 = 1 + q ^ 2 + x ^ 2 := by omega
  have hyB' : y ∈ B := by
    rw [hyB]
    exact Finset.mem_singleton_self y
  have hyE : y ∈ E := hBsub hyB'
  rw [hEeq] at hyE
  simp only [Finset.mem_insert, Finset.mem_singleton] at hyE
  rcases hyE with rfl | hyq | hyx
  · norm_num at heq
    have hq9 : 9 ≤ q ^ 2 := by
      calc (9 : ℕ) = 3 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left h3 2
    omega
  · rw [hyq] at heq
    have hq34 : q = 3 ∨ q = 4 := by omega
    rcases hq34 with rfl | rfl
    · have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
      rw [h9] at heq
      have hx8 : x ^ 2 = 8 := by omega
      exact not_sq_mem hx8 (Or.inl rfl)
    · have h16 : (4 : ℕ) ^ 2 = 16 := by norm_num
      rw [h16] at heq
      have hx15 : x ^ 2 = 15 := by omega
      exact not_sq_mem hx15 (Or.inr (Or.inr (Or.inl rfl)))
  · rw [hyx] at heq
    have hq34 : q = 3 ∨ q = 4 := by omega
    rcases hq34 with rfl | rfl
    · have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
      rw [h9] at heq
      have hx10 : x ^ 2 = 10 := by omega
      exact not_sq_mem hx10 (Or.inr (Or.inl rfl))
    · have h16 : (4 : ℕ) ^ 2 = 16 := by norm_num
      rw [h16] at heq
      have hx17 : x ^ 2 = 17 := by omega
      exact not_sq_mem hx17 (Or.inr (Or.inr (Or.inr rfl)))

/-- With least unitary divisor three or four there are over two prime factors. -/
private theorem two_lt_card_of_isUnitarySZumkeller {n q : ℕ} (h : IsUnitarySZumkeller n)
    (hq : IsLeast {d | d ∈ Nat.unitaryDivisors n ∧ 1 < d} q)
    (h3 : 3 ≤ q) (h4 : q ≤ 4) : 2 < n.primeFactors.card := by
  have hn := ne_zero_of_isUnitarySZumkeller h
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hqmem : q ∈ Nat.unitaryDivisors n ∧ 1 < q := hq.1
  obtain ⟨A, hAsub, hAne, hBne, hbal⟩ := h
  have hnmem : n ∈ Nat.unitaryDivisors n := self_mem_unitaryDivisors hn
  have hcard := card_unitaryDivisors n hn
  by_contra hcon
  have hcon' : n.primeFactors.card ≤ 2 := by omega
  have hEcard : ((Nat.unitaryDivisors n).erase n).card = 2 ^ n.primeFactors.card - 1 := by
    rw [Finset.card_erase_of_mem hnmem, hcard]
  have hApos : 0 < A.card := Finset.card_pos.mpr hAne
  have hBpos : 0 < ((Nat.unitaryDivisors n).erase n \ A).card := Finset.card_pos.mpr hBne
  have hsum := Finset.card_sdiff_add_card_eq_card hAsub
  have h2le : 2 ≤ ((Nat.unitaryDivisors n).erase n).card := by omega
  rw [hEcard] at h2le
  have h2m : 2 ≤ n.primeFactors.card := by
    by_contra hc
    have hc1 : n.primeFactors.card ≤ 1 := by omega
    have hpow : 2 ^ n.primeFactors.card ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) hc1
    norm_num at hpow
    omega
  have hm2 : n.primeFactors.card = 2 := by omega
  have hEcard3 : ((Nat.unitaryDivisors n).erase n).card = 3 := by
    rw [hEcard, hm2]
    norm_num
  have hqn : q ∣ n := (Nat.mem_unitaryDivisors.mp hqmem.1).1
  have hqn_le : q ≤ n := Nat.le_of_dvd hn0 hqn
  have hn6 : 6 ≤ n := by
    obtain ⟨p₁, hp₁, p₂, hp₂, hne⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < n.primeFactors.card)
    have hpr₁ := Nat.prime_of_mem_primeFactors hp₁
    have hpr₂ := Nat.prime_of_mem_primeFactors hp₂
    have hcop : p₁.Coprime p₂ := (Nat.coprime_primes hpr₁ hpr₂).mpr hne
    have hdvd : p₁ * p₂ ∣ n :=
      hcop.mul_dvd_of_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp₁)
        (Nat.dvd_of_mem_primeFactors hp₂)
    have hle : p₁ * p₂ ≤ n := Nat.le_of_dvd hn0 hdvd
    have h2₁ := hpr₁.two_le
    have h2₂ := hpr₂.two_le
    have h6 : 6 ≤ p₁ * p₂ := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h3₂ : 3 ≤ p₂ := by omega
        calc (6 : ℕ) = 2 * 3 := by norm_num
          _ ≤ p₁ * p₂ := Nat.mul_le_mul h2₁ h3₂
      · have h3₁ : 3 ≤ p₁ := by omega
        calc (6 : ℕ) = 3 * 2 := by norm_num
          _ ≤ p₁ * p₂ := Nat.mul_le_mul h3₁ h2₂
    omega
  have h1mem : 1 ∈ (Nat.unitaryDivisors n).erase n := by
    rw [Finset.mem_erase]
    refine ⟨?_, one_mem_unitaryDivisors hn⟩
    have h1q : (1 : ℕ) < q := hqmem.2
    omega
  have hqmemE : q ∈ (Nat.unitaryDivisors n).erase n := by
    rw [Finset.mem_erase]
    refine ⟨?_, hqmem.1⟩
    omega
  have h1q : (1 : ℕ) ≠ q := by
    have h1q' : (1 : ℕ) < q := hqmem.2
    omega
  have hsub : ({1, q} : Finset ℕ) ⊆ (Nat.unitaryDivisors n).erase n := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact h1mem
    · exact hqmemE
  have h1nmem : (1 : ℕ) ∉ ({q} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    exact h1q
  have hcard1q : ({1, q} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem h1nmem, Finset.card_singleton]
  obtain ⟨x, hx⟩ : ∃ x, (Nat.unitaryDivisors n).erase n \ {1, q} = {x} := by
    have hcc := Finset.card_sdiff_add_card_eq_card hsub
    rw [hEcard3, hcard1q] at hcc
    have h1 : ((Nat.unitaryDivisors n).erase n \ {1, q}).card = 1 := by omega
    exact Finset.card_eq_one.mp h1
  have hEeq : (Nat.unitaryDivisors n).erase n = {1, q, x} := by
    have h1 : (Nat.unitaryDivisors n).erase n \ {1, q} ∪ {1, q}
        = (Nat.unitaryDivisors n).erase n :=
      Finset.sdiff_union_of_subset hsub
    rw [hx] at h1
    have h2 : ({x} ∪ {1, q} : Finset ℕ) = {1, q, x} := by
      ext y
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [h2] at h1
    exact h1.symm
  have hxmem : x ∈ (Nat.unitaryDivisors n).erase n \ {1, q} := by
    rw [hx]
    exact Finset.mem_singleton_self x
  rw [Finset.mem_sdiff] at hxmem
  have hxne : x ≠ 1 ∧ x ≠ q := by
    simpa using hxmem.2
  have hcard3 : A.card + ((Nat.unitaryDivisors n).erase n \ A).card = 3 := by
    have hcc := Finset.card_sdiff_add_card_eq_card hAsub
    rw [hEcard3] at hcc
    omega
  have hwlog : A.card = 1 ∨ ((Nat.unitaryDivisors n).erase n \ A).card = 1 := by omega
  rcases hwlog with hA1 | hB1
  · exact nosplit_of_singleton hAsub hA1 hbal hEeq h1q hxne.1 hxne.2 h3 h4
  · have hBsub : (Nat.unitaryDivisors n).erase n \ A ⊆ (Nat.unitaryDivisors n).erase n :=
      Finset.sdiff_subset
    have hEE : (Nat.unitaryDivisors n).erase n \ ((Nat.unitaryDivisors n).erase n \ A) = A :=
      Finset.sdiff_sdiff_eq_self hAsub
    have hsumB : ∑ d ∈ (Nat.unitaryDivisors n).erase n \ A, d ^ 2
        = ∑ d ∈ (Nat.unitaryDivisors n).erase n \ ((Nat.unitaryDivisors n).erase n \ A),
          d ^ 2 := by
      rw [hEE]
      exact hbal.symm
    exact nosplit_of_singleton hBsub hB1 hsumB hEeq h1q hxne.1 hxne.2 h3 h4

/-- With least unitary divisor two there are over six prime factors. -/
private theorem six_lt_card_of_isUnitarySZumkeller {n : ℕ} (h : IsUnitarySZumkeller n)
    (hq : IsLeast {d | d ∈ Nat.unitaryDivisors n ∧ 1 < d} 2) :
    6 < n.primeFactors.card := by
  by_contra hcon
  have hm6 : n.primeFactors.card ≤ 6 := by omega
  -- Proposition 11 at `q = 2`: the left side is `3 / 2`.
  have hb := (isUnitarySZumkeller_bounds n 2 h hq).2.2
  have h32 : (2 : ℚ) / ((2 : ℕ) : ℚ) ^ 2 + 1 = 3 / 2 := by norm_num
  rw [h32] at hb
  have hfactor : ∀ p ∈ n.primeFactors,
      (1 + ((p : ℚ) ^ n.factorization p) ^ 2) / ((p : ℚ) ^ n.factorization p) ^ 2
        ≤ 1 + 1 / (p : ℚ) ^ 2 := by
    intro p hp
    have hpp : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hk : 1 ≤ n.factorization p := by
      have hmem : p ∈ n.factorization.support := by rwa [Nat.support_factorization]
      have hne := Finsupp.mem_support_iff.mp hmem
      omega
    have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 0 < p)
    have hx0 : (0 : ℚ) < (p : ℚ) ^ n.factorization p := pow_pos hp0 _
    have hsplit : (1 + ((p : ℚ) ^ n.factorization p) ^ 2) / ((p : ℚ) ^ n.factorization p) ^ 2
        = 1 + 1 / ((p : ℚ) ^ n.factorization p) ^ 2 := by
      rw [add_div, div_self (pow_ne_zero 2 hx0.ne'), add_comm]
    rw [hsplit]
    have hle : (p : ℚ) ≤ (p : ℚ) ^ n.factorization p := by
      calc (p : ℚ) = (p : ℚ) ^ 1 := (pow_one _).symm
        _ ≤ (p : ℚ) ^ n.factorization p :=
          pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ p)) hk
    have hleQ : (p : ℚ) ^ 2 ≤ ((p : ℚ) ^ n.factorization p) ^ 2 :=
      pow_le_pow_left₀ hp0.le hle 2
    have hdiv := one_div_le_one_div_of_le (pow_pos hp0 2) hleQ
    linarith
  have hprod_le : ∏ p ∈ n.primeFactors,
      (1 + ((p : ℚ) ^ n.factorization p) ^ 2) / ((p : ℚ) ^ n.factorization p) ^ 2
        ≤ ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℚ) ^ 2) := by
    apply Finset.prod_le_prod₀ _ hfactor
    intro p _
    positivity
  have hsorted : ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℚ) ^ 2)
      ≤ ∏ j ∈ Finset.range n.primeFactors.card, (1 + 1 / (smallPrime j : ℚ) ^ 2) :=
    prod_le_smallPrimes_prod n.primeFactors.card hm6 n.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp) rfl
  have hmono : ∏ j ∈ Finset.range n.primeFactors.card, (1 + 1 / (smallPrime j : ℚ) ^ 2)
      ≤ ∏ j ∈ Finset.range 6, (1 + 1 / (smallPrime j : ℚ) ^ 2) := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.range_mono hm6) _ _
    · intro j _
      positivity
    · intro j _ _
      exact le_add_of_nonneg_right (one_div_nonneg.mpr (sq_nonneg _))
  have hF6 : ∏ j ∈ Finset.range 6, (1 + 1 / (smallPrime j : ℚ) ^ 2) < 3 / 2 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, Finset.prod_range_succ,
      show (5 : ℕ) = 4 + 1 from rfl, Finset.prod_range_succ,
      show (4 : ℕ) = 3 + 1 from rfl, Finset.prod_range_succ,
      show (3 : ℕ) = 2 + 1 from rfl, Finset.prod_range_succ,
      show (2 : ℕ) = 1 + 1 from rfl, Finset.prod_range_succ,
      show (1 : ℕ) = 0 + 1 from rfl, Finset.prod_range_succ, Finset.prod_range_zero]
    norm_num [smallPrime]
  linarith [hb, hprod_le, hsorted, hmono, hF6]

/-- **Unitary divisor counts of unitary s-Zumkeller numbers.** Let $n$ be a unitary s-Zumkeller
number and let $q$ be the least unitary divisor of $n$ greater than $1$. If $q = 2$, then $n$ has
more than $2^6$ unitary divisors; if $q = 3$ or $q = 4$, then $n$ has more than $2^2$ unitary
divisors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 12. -/
public theorem card_unitaryDivisors_of_isUnitarySZumkeller (n q : ℕ)
    (h : IsUnitarySZumkeller n) (hq : IsLeast {d | d ∈ Nat.unitaryDivisors n ∧ 1 < d} q) :
    (q = 2 → 2 ^ 6 < (Nat.unitaryDivisors n).card) ∧
      (q = 3 → 2 ^ 2 < (Nat.unitaryDivisors n).card) ∧
      (q = 4 → 2 ^ 2 < (Nat.unitaryDivisors n).card) := by
  have hn := ne_zero_of_isUnitarySZumkeller h
  rw [card_unitaryDivisors n hn]
  refine ⟨?_, ?_, ?_⟩
  · intro hq2
    subst hq2
    have h6 := six_lt_card_of_isUnitarySZumkeller h hq
    exact pow_lt_pow_right₀ (by norm_num) h6
  · intro hq3
    subst hq3
    have h2 := two_lt_card_of_isUnitarySZumkeller h hq (by norm_num) (by norm_num)
    exact pow_lt_pow_right₀ (by norm_num) h2
  · intro hq4
    subst hq4
    have h2 := two_lt_card_of_isUnitarySZumkeller h hq (by norm_num) (by norm_num)
    exact pow_lt_pow_right₀ (by norm_num) h2

end

end MetaMathlibExt
