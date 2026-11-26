/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SZumkeller
import MathlibExt.NumberTheory.UnitaryDivisorCount
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

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

-- The construction `unitaryFromSubset` and the proofs below that it inverts the prime-factor
-- set of a unitary divisor adapt the proof of `MetaMathlibExt.card_unitaryDivisors` in
-- `MathlibExt/NumberTheory/UnitaryDivisorCount.lean`.
/-- The unitary divisor assembled from the prime powers indexed by a set. -/
private def unitaryFromSubset (n : ℕ) (s : Finset ℕ) : ℕ :=
  (n.factorization.filter (· ∈ s)).prod (· ^ ·)

/-- The filtered factorization sits below the full factorization. -/
private theorem unitaryFromSubset_le (n : ℕ) (s : Finset ℕ) :
    n.factorization.filter (· ∈ s) ≤ n.factorization := by
  rw [Finsupp.le_def]
  intro p
  by_cases hp : p ∈ s <;> simp [hp]

/-- The factorization of the assembled divisor is the filtered factorization. -/
private theorem unitaryFromSubset_factorization (n : ℕ) (s : Finset ℕ) :
    (unitaryFromSubset n s).factorization = n.factorization.filter (· ∈ s) :=
  Nat.factorization_prod_pow_eq_self_of_le_factorization (unitaryFromSubset_le n s)

/-- The prime factors of the assembled divisor are the selected primes. -/
private theorem unitaryFromSubset_primeFactors (n : ℕ) (s : Finset ℕ) :
    (unitaryFromSubset n s).primeFactors = n.primeFactors.filter (· ∈ s) := by
  rw [← Nat.support_factorization, unitaryFromSubset_factorization,
    Finsupp.support_filter, Nat.support_factorization]

/-- The assembled divisor is a unitary divisor. -/
private theorem unitaryFromSubset_mem (n : ℕ) (hn : n ≠ 0) (s : Finset ℕ) :
    unitaryFromSubset n s ∈ Nat.unitaryDivisors n := by
  have hdvd : unitaryFromSubset n s ∣ n :=
    Nat.prod_pow_dvd_of_le_factorization (unitaryFromSubset_le n s)
  have hd0 : unitaryFromSubset n s ≠ 0 := ne_zero_of_dvd_ne_zero hn hdvd
  have hq0 : n / unitaryFromSubset n s ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd)
      (Nat.pos_of_ne_zero hd0)).ne'
  refine Nat.mem_unitaryDivisors.mpr ⟨hdvd, hn, (Nat.disjoint_primeFactors hd0 hq0).mp ?_⟩
  rw [Finset.disjoint_left]
  intro p hp hq
  rw [unitaryFromSubset_primeFactors, Finset.mem_filter] at hp
  have hz : (n / unitaryFromSubset n s).factorization p = 0 := by
    rw [Nat.factorization_div hdvd, Finsupp.tsub_apply, unitaryFromSubset_factorization]
    simp [hp.2]
  exact (Finsupp.notMem_support_iff.mpr hz) hq

/-- Assembling over a subset of the prime factors inverts taking prime factors. -/
private theorem unitaryFromSubset_primeFactors_of_mem (n : ℕ) (s : Finset ℕ)
    (hs : s ∈ n.primeFactors.powerset) :
    (unitaryFromSubset n s).primeFactors = s := by
  rw [unitaryFromSubset_primeFactors]
  ext p
  rw [Finset.mem_filter]
  exact ⟨And.right, fun hp => ⟨Finset.mem_powerset.mp hs hp, hp⟩⟩

/-- Every unitary divisor is assembled from its prime factors. -/
private theorem unitaryFromSubset_of_primeFactors (n : ℕ) (hn : n ≠ 0) (d : ℕ)
    (hd : d ∈ Nat.unitaryDivisors n) : unitaryFromSubset n d.primeFactors = d := by
  obtain ⟨hdvd, _, hcop⟩ := Nat.mem_unitaryDivisors.mp hd
  change (n.factorization.filter (· ∈ d.primeFactors)).prod (· ^ ·) = d
  suffices h : n.factorization.filter (· ∈ d.primeFactors) = d.factorization by
    rw [h, Nat.prod_factorization_pow_eq_self (ne_zero_of_dvd_ne_zero hn hdvd)]
  ext p
  by_cases hp : p ∈ d.primeFactors
  · rw [Finsupp.filter_apply_pos _ _ hp, ← Nat.div_mul_cancel hdvd,
      Nat.factorization_eq_of_coprime_right hcop.symm
        (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp)]
  · rw [Finsupp.filter_apply_neg _ _ hp, Finsupp.notMem_support_iff.mp hp]

/-- The assembled divisor is the product of the selected prime powers. -/
private theorem unitaryFromSubset_prod (n : ℕ) (s : Finset ℕ)
    (hs : s ∈ n.primeFactors.powerset) :
    unitaryFromSubset n s = ∏ p ∈ s, p ^ n.factorization p := by
  have hsub : s ⊆ n.primeFactors := Finset.mem_powerset.mp hs
  change (n.factorization.filter (· ∈ s)).prod (· ^ ·) = _
  rw [Finsupp.prod_filter_index]
  have hset : (n.factorization.filter (· ∈ s)).support = s := by
    rw [Finsupp.support_filter, Nat.support_factorization]
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun h => ⟨hsub h, h⟩⟩
  rw [hset]

/-- A multiplicative sum over unitary divisors is a product over prime factors. -/
private theorem sum_unitaryDivisors_eq_prod {n : ℕ} (hn : n ≠ 0) (g : ℕ → ℚ)
    (g1 : g 1 = 1) (gmul : ∀ a b, g (a * b) = g a * g b) :
    ∑ d ∈ Nat.unitaryDivisors n, g d =
      ∏ p ∈ n.primeFactors, (1 + g (p ^ n.factorization p)) := by
  have hmul : ∀ s ∈ n.primeFactors.powerset,
      g (unitaryFromSubset n s) = ∏ p ∈ s, g (p ^ n.factorization p) := by
    intro s hs
    rw [unitaryFromSubset_prod n s hs]
    clear hs
    induction s using Finset.induction with
    | empty => simp [g1]
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, gmul, ih]
  have hbij : ∑ d ∈ Nat.unitaryDivisors n, g d
      = ∑ s ∈ n.primeFactors.powerset, g (unitaryFromSubset n s) := by
    apply Finset.sum_bij (fun d _ => d.primeFactors)
    · intro d hd
      exact Finset.mem_powerset.mpr
        (Nat.primeFactors_mono (Nat.dvd_of_mem_unitaryDivisors hd) hn)
    · intro d₁ hd₁ d₂ hd₂ heq
      have e1 := unitaryFromSubset_of_primeFactors n hn d₁ hd₁
      have e2 := unitaryFromSubset_of_primeFactors n hn d₂ hd₂
      have heq' : d₁.primeFactors = d₂.primeFactors := heq
      rw [heq'] at e1
      exact e1.symm.trans e2
    · intro s hs
      exact ⟨unitaryFromSubset n s, unitaryFromSubset_mem n hn s,
        unitaryFromSubset_primeFactors_of_mem n s hs⟩
    · intro d hd
      show g d = g (unitaryFromSubset n d.primeFactors)
      rw [unitaryFromSubset_of_primeFactors n hn d hd]
  rw [hbij]
  trans ∑ s ∈ n.primeFactors.powerset, ∏ p ∈ s, g (p ^ n.factorization p)
  · apply Finset.sum_congr rfl
    intro s hs
    exact hmul s hs
  · have hpa := Finset.prod_add (fun p => g (p ^ n.factorization p)) (fun _ => 1)
      n.primeFactors
    simpa [add_comm] using hpa.symm

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
  have hn := ne_zero_of_isUnitarySZumkeller h
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hqmem : 2 ∈ Nat.unitaryDivisors n ∧ 1 < 2 := hq.1
  have h2dvd : 2 ∣ n := (Nat.mem_unitaryDivisors.mp hqmem.1).1
  have hnmem : n ∈ Nat.unitaryDivisors n := self_mem_unitaryDivisors hn
  by_contra hcon
  have hm6 : n.primeFactors.card ≤ 6 := by omega
  obtain ⟨A, hAsub, _, _, hbal⟩ := h
  have h2e : n / 2 * 2 = n := Nat.div_mul_cancel h2dvd
  have hemem : n / 2 ∈ Nat.unitaryDivisors n := by
    rw [Nat.mem_unitaryDivisors]
    refine ⟨Nat.div_dvd_of_dvd h2dvd, hn, ?_⟩
    have hne : n / (n / 2) = 2 := Nat.div_div_self h2dvd hn
    rw [hne]
    exact (Nat.coprime_div_of_mem_unitaryDivisors hqmem.1).symm
  have hene : n / 2 ≠ n := by
    have hlt : n / 2 < n := Nat.div_lt_self hn0 (by norm_num)
    omega
  have heE : n / 2 ∈ (Nat.unitaryDivisors n).erase n := Finset.mem_erase.mpr ⟨hene, hemem⟩
  have hTe : (n / 2) ^ 2 ≤ ∑ d ∈ A, d ^ 2 := by
    by_cases heA : n / 2 ∈ A
    · exact Finset.single_le_sum (f := fun d : ℕ => d ^ 2) (fun _ _ => Nat.zero_le _) heA
    · have heB : n / 2 ∈ (Nat.unitaryDivisors n).erase n \ A :=
        Finset.mem_sdiff.mpr ⟨heE, heA⟩
      have hle : (n / 2) ^ 2 ≤ ∑ d ∈ (Nat.unitaryDivisors n).erase n \ A, d ^ 2 :=
        Finset.single_le_sum (f := fun d : ℕ => d ^ 2) (fun _ _ => Nat.zero_le _) heB
      omega
  have hUD : Nat.unitaryDivisors n = insert n ((Nat.unitaryDivisors n).erase n) :=
    (Finset.insert_erase hnmem).symm
  have hsumUD : ∑ d ∈ Nat.unitaryDivisors n, d ^ 2 = n ^ 2 + 2 * ∑ d ∈ A, d ^ 2 := by
    have hsplit := Finset.sum_sdiff (f := fun d : ℕ => d ^ 2) hAsub
    rw [hUD, Finset.sum_insert (Finset.notMem_erase n _)]
    omega
  have hcast : (3 / 2 : ℚ) ≤ ∑ d ∈ Nat.unitaryDivisors n, ((d : ℚ) / (n : ℚ)) ^ 2 := by
    have hnQ2 : (0 : ℚ) < (n : ℚ) ^ 2 := pow_pos (by exact_mod_cast hn0) 2
    have h2eQ : (((n / 2 : ℕ)) : ℚ) * 2 = (n : ℚ) := by exact_mod_cast h2e
    have hkey : (3 / 2 : ℚ) * (n : ℚ) ^ 2 ≤ ∑ d ∈ Nat.unitaryDivisors n, (d : ℚ) ^ 2 := by
      have hnat : (n : ℚ) ^ 2 + 2 * ((((n / 2 : ℕ))) : ℚ) ^ 2
          ≤ ∑ d ∈ Nat.unitaryDivisors n, (d : ℚ) ^ 2 := by
        have h1 : n ^ 2 + 2 * (n / 2) ^ 2 ≤ ∑ d ∈ Nat.unitaryDivisors n, d ^ 2 := by omega
        exact_mod_cast h1
      have h4 : (n : ℚ) ^ 2 = 4 * ((((n / 2 : ℕ))) : ℚ) ^ 2 := by
        rw [← h2eQ]
        ring
      linarith [hnat, h4]
    have hdiv : ∑ d ∈ Nat.unitaryDivisors n, ((d : ℚ) / (n : ℚ)) ^ 2
        = (∑ d ∈ Nat.unitaryDivisors n, (d : ℚ) ^ 2) / (n : ℚ) ^ 2 := by
      simp only [div_pow]
      simp only [div_eq_mul_inv, Finset.sum_mul]
    rw [hdiv]
    exact (le_div_iff₀ hnQ2).mpr hkey
  have hreidx : ∑ d ∈ Nat.unitaryDivisors n, ((d : ℚ) / (n : ℚ)) ^ 2
      = ∑ e ∈ Nat.unitaryDivisors n, 1 / (e : ℚ) ^ 2 := by
    apply Finset.sum_bij (fun d _ => n / d)
    · intro d hd
      show n / d ∈ Nat.unitaryDivisors n
      rw [Nat.mem_unitaryDivisors] at hd ⊢
      obtain ⟨hdvd, _, hcop⟩ := hd
      refine ⟨Nat.div_dvd_of_dvd hdvd, hn, ?_⟩
      have hdd : n / (n / d) = d := Nat.div_div_self hdvd hn
      rw [hdd]
      exact hcop.symm
    · intro d₁ hd₁ d₂ hd₂ heq
      have heq' : n / d₁ = n / d₂ := heq
      have hdvd₁ := (Nat.mem_unitaryDivisors.mp hd₁).1
      have hdvd₂ := (Nat.mem_unitaryDivisors.mp hd₂).1
      have e1 := Nat.div_div_self hdvd₁ hn
      have e2 := Nat.div_div_self hdvd₂ hn
      rw [heq'] at e1
      exact e1.symm.trans e2
    · intro e he
      have hmem : n / e ∈ Nat.unitaryDivisors n := by
        rw [Nat.mem_unitaryDivisors] at he ⊢
        obtain ⟨hdvd, _, hcop⟩ := he
        refine ⟨Nat.div_dvd_of_dvd hdvd, hn, ?_⟩
        have hdd : n / (n / e) = e := Nat.div_div_self hdvd hn
        rw [hdd]
        exact hcop.symm
      exact ⟨n / e, hmem, Nat.div_div_self (Nat.dvd_of_mem_unitaryDivisors he) hn⟩
    · intro d hd
      show ((d : ℚ) / (n : ℚ)) ^ 2 = 1 / ((((n / d : ℕ))) : ℚ) ^ 2
      have hdvd := Nat.dvd_of_mem_unitaryDivisors hd
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [zero_dvd_iff] at hdvd
        exact hn hdvd
      have hnd0 : n / d ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd hn0 hdvd) (Nat.pos_of_ne_zero hd0)).ne'
      have hde : d * (n / d) = n := by
        rw [mul_comm]
        exact Nat.div_mul_cancel hdvd
      have hdeQ : (d : ℚ) * ((((n / d : ℕ))) : ℚ) = (n : ℚ) := by exact_mod_cast hde
      have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
      have hndQ : ((((n / d : ℕ))) : ℚ) ≠ 0 := by exact_mod_cast hnd0
      have hfrac : (d : ℚ) / (n : ℚ) = ((((n / d : ℕ))) : ℚ)⁻¹ := by
        field_simp
        linear_combination hdeQ
      rw [hfrac, inv_pow, one_div]
  have hsumprod : ∑ e ∈ Nat.unitaryDivisors n, 1 / (e : ℚ) ^ 2
      = ∏ p ∈ n.primeFactors, (1 + 1 / ((((p ^ n.factorization p : ℕ))) : ℚ) ^ 2) := by
    have h := sum_unitaryDivisors_eq_prod hn (fun d : ℕ => 1 / (d : ℚ) ^ 2)
      (by norm_num) (by
        intro a b
        show 1 / ((((a * b : ℕ))) : ℚ) ^ 2 = 1 / (a : ℚ) ^ 2 * (1 / (b : ℚ) ^ 2)
        rw [Nat.cast_mul, mul_pow, ← one_div_mul_one_div])
    exact h
  have hfactor : ∀ p ∈ n.primeFactors,
      (1 : ℚ) + 1 / ((((p ^ n.factorization p : ℕ))) : ℚ) ^ 2
        ≤ 1 + 1 / (p : ℚ) ^ 2 := by
    intro p hp
    have hpp : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hk : 1 ≤ n.factorization p := by
      have hmem : p ∈ n.factorization.support := by rwa [Nat.support_factorization]
      have hne := Finsupp.mem_support_iff.mp hmem
      omega
    have hle : p ^ 1 ≤ p ^ n.factorization p := pow_le_pow_right₀ (by omega) hk
    have hleQ : (p : ℚ) ^ 2 ≤ ((((p ^ n.factorization p : ℕ))) : ℚ) ^ 2 := by
      have h1 : (p : ℚ) ≤ ((((p ^ n.factorization p : ℕ))) : ℚ) := by
        have h2 : p ≤ p ^ n.factorization p := by
          simpa using hle
        exact_mod_cast h2
      have ha0 : (0 : ℚ) ≤ (p : ℚ) := by positivity
      exact pow_le_pow_left₀ ha0 h1 2
    have hpos : (0 : ℚ) < (p : ℚ) ^ 2 := pow_pos (by exact_mod_cast (by omega : 0 < p)) 2
    have hdiv := one_div_le_one_div_of_le hpos hleQ
    linarith
  have hprod_le : ∏ p ∈ n.primeFactors, ((1 : ℚ) + 1 / ((((p ^ n.factorization p : ℕ))) : ℚ) ^ 2)
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
  linarith [hcast, hreidx, hsumprod, hprod_le, hsorted, hmono, hF6]

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
