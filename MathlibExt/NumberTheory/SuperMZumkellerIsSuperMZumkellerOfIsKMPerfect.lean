/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SuperMZumkeller
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Ring

/-!
# `k`-m-perfect numbers with `4 ∣ k` are super-m-Zumkeller

Every `k`-m-perfect number with `k ≥ 2` and `k ≡ 0 mod 4` is super-m-Zumkeller,
via an equal-product split of the divisors of a fourth power.

Source: Harish Patodia, "Super m-Zumkeller Numbers", Theorem 6.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.SuperMZumkellerWanted

open Finset

private theorem sum_ite_good_range (m : ℕ) :
    ∑ e ∈ Finset.range (4 * m + 1),
      (if e % 4 = 0 ∨ e % 4 = 1 then e else 0) = m * (4 * m + 1) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have hstep : 4 * (m + 1) + 1 = (4 * m + 1) + 4 := by ring
    rw [hstep]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
    have h1 : (if (4 * m + 1) % 4 = 0 ∨ (4 * m + 1) % 4 = 1 then 4 * m + 1 else 0)
        = 4 * m + 1 := ite_eq_left (Or.inr (by omega))
    have h2 : (if (4 * m + 2) % 4 = 0 ∨ (4 * m + 2) % 4 = 1 then 4 * m + 2 else 0)
        = 0 := ite_eq_right (by omega)
    have h3 : (if (4 * m + 3) % 4 = 0 ∨ (4 * m + 3) % 4 = 1 then 4 * m + 3 else 0)
        = 0 := ite_eq_right (by omega)
    have h4 : (if (4 * m + 4) % 4 = 0 ∨ (4 * m + 4) % 4 = 1 then 4 * m + 4 else 0)
        = 4 * m + 4 := ite_eq_left (Or.inl (by omega))
    rw [h1, h2, h3, h4, ih]
    ring

private theorem sum_ite_not_good_range (m : ℕ) :
    ∑ e ∈ Finset.range (4 * m + 1),
      (if ¬(e % 4 = 0 ∨ e % 4 = 1) then e else 0) = m * (4 * m + 1) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have hstep : 4 * (m + 1) + 1 = (4 * m + 1) + 4 := by ring
    rw [hstep]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
    have h1 : (if ¬((4 * m + 1) % 4 = 0 ∨ (4 * m + 1) % 4 = 1) then 4 * m + 1 else 0)
        = 0 := ite_eq_right (by omega)
    have h2 : (if ¬((4 * m + 2) % 4 = 0 ∨ (4 * m + 2) % 4 = 1) then 4 * m + 2 else 0)
        = 4 * m + 2 := ite_eq_left (by omega)
    have h3 : (if ¬((4 * m + 3) % 4 = 0 ∨ (4 * m + 3) % 4 = 1) then 4 * m + 3 else 0)
        = 4 * m + 3 := ite_eq_left (by omega)
    have h4 : (if ¬((4 * m + 4) % 4 = 0 ∨ (4 * m + 4) % 4 = 1) then 4 * m + 4 else 0)
        = 0 := ite_eq_right (by omega)
    rw [h1, h2, h3, h4, ih]
    ring

private def goodResidue (d p : ℕ) : Prop := d.factorization p % 4 = 0 ∨ d.factorization p % 4 = 1

private instance decidableGoodResidue (d p : ℕ) : Decidable (goodResidue d p) := by
  unfold goodResidue
  infer_instance

private theorem sum_filter_good_prime_pow (q m : ℕ) (hq : q.Prime) :
    ∑ a ∈ (q ^ (4 * m)).divisors.filter (fun a => goodResidue a q),
      a.factorization q = m * (4 * m + 1) := by
  rw [Finset.sum_filter, Nat.sum_divisors_prime_pow hq]
  have hpt : ∀ x : ℕ, (if goodResidue (q ^ x) q then (q ^ x).factorization q else 0)
      = (if x % 4 = 0 ∨ x % 4 = 1 then x else 0) := by
    intro x
    have hfx : (q ^ x).factorization q = x := Nat.factorization_pow_self hq
    simp only [goodResidue, hfx]
  exact (Finset.sum_congr rfl (fun x _ => hpt x)).trans (sum_ite_good_range m)

private theorem sum_filter_not_good_prime_pow (q m : ℕ) (hq : q.Prime) :
    ∑ a ∈ (q ^ (4 * m)).divisors.filter (fun a => ¬goodResidue a q),
      a.factorization q = m * (4 * m + 1) := by
  rw [Finset.sum_filter, Nat.sum_divisors_prime_pow hq]
  have hpt : ∀ x : ℕ, (if ¬goodResidue (q ^ x) q then (q ^ x).factorization q else 0)
      = (if ¬(x % 4 = 0 ∨ x % 4 = 1) then x else 0) := by
    intro x
    have hfx : (q ^ x).factorization q = x := Nat.factorization_pow_self hq
    simp only [goodResidue, hfx]
  exact (Finset.sum_congr rfl (fun x _ => hpt x)).trans (sum_ite_not_good_range m)

private theorem inner_sum_even_pos (q m R : ℕ) (hq : q.Prime) (hR : R % 2 = 0) :
    (∑ a ∈ (q ^ (4 * m)).divisors,
      (if (R + (if goodResidue a q then 1 else 0)) % 2 = 0 then a.factorization q
        else 0)) = m * (4 * m + 1) := by
  have hiff : ∀ a : ℕ, ((R + (if goodResidue a q then 1 else 0)) % 2 = 0) ↔
      ¬goodResidue a q := by
    intro a
    by_cases h : goodResidue a q
    · rw [ite_eq_left h]
      have hfalse : ¬(R + 1) % 2 = 0 := by omega
      simp [hfalse, h]
    · rw [ite_eq_right h]
      simp [hR, h]
  have hsum : (∑ a ∈ (q ^ (4 * m)).divisors,
        (if (R + (if goodResidue a q then 1 else 0)) % 2 = 0 then a.factorization q
          else 0))
      = ∑ a ∈ (q ^ (4 * m)).divisors.filter (fun a => ¬goodResidue a q),
        a.factorization q := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    simp only [hiff a]
  exact hsum.trans (sum_filter_not_good_prime_pow q m hq)

private theorem inner_sum_even_neg (q m R : ℕ) (hq : q.Prime) (hR : R % 2 = 0) :
    (∑ a ∈ (q ^ (4 * m)).divisors,
      (if ¬(R + (if goodResidue a q then 1 else 0)) % 2 = 0 then a.factorization q
        else 0)) = m * (4 * m + 1) := by
  have hiff : ∀ a : ℕ, (¬(R + (if goodResidue a q then 1 else 0)) % 2 = 0) ↔
      goodResidue a q := by
    intro a
    by_cases h : goodResidue a q
    · rw [ite_eq_left h]
      have hfalse : ¬(R + 1) % 2 = 0 := by omega
      simp [hfalse, h]
    · rw [ite_eq_right h]
      simp [hR, h]
  have hsum : (∑ a ∈ (q ^ (4 * m)).divisors,
        (if ¬(R + (if goodResidue a q then 1 else 0)) % 2 = 0 then a.factorization q
          else 0))
      = ∑ a ∈ (q ^ (4 * m)).divisors.filter (fun a => goodResidue a q),
        a.factorization q := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    simp only [hiff a]
  exact hsum.trans (sum_filter_good_prime_pow q m hq)

private theorem inner_sum_odd_pos (q m R : ℕ) (hq : q.Prime) (hR : R % 2 = 1) :
    (∑ a ∈ (q ^ (4 * m)).divisors,
      (if (R + (if goodResidue a q then 1 else 0)) % 2 = 0 then a.factorization q
        else 0)) = m * (4 * m + 1) := by
  have hiff : ∀ a : ℕ, ((R + (if goodResidue a q then 1 else 0)) % 2 = 0) ↔
      goodResidue a q := by
    intro a
    by_cases h : goodResidue a q
    · rw [ite_eq_left h]
      have htrue : (R + 1) % 2 = 0 := by omega
      simp [htrue, h]
    · rw [ite_eq_right h]
      simp [hR, h]
  have hsum : (∑ a ∈ (q ^ (4 * m)).divisors,
        (if (R + (if goodResidue a q then 1 else 0)) % 2 = 0 then a.factorization q
          else 0))
      = ∑ a ∈ (q ^ (4 * m)).divisors.filter (fun a => goodResidue a q),
        a.factorization q := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    simp only [hiff a]
  exact hsum.trans (sum_filter_good_prime_pow q m hq)

private theorem inner_sum_odd_neg (q m R : ℕ) (hq : q.Prime) (hR : R % 2 = 1) :
    (∑ a ∈ (q ^ (4 * m)).divisors,
      (if ¬(R + (if goodResidue a q then 1 else 0)) % 2 = 0 then a.factorization q
        else 0)) = m * (4 * m + 1) := by
  have hiff : ∀ a : ℕ, (¬(R + (if goodResidue a q then 1 else 0)) % 2 = 0) ↔
      ¬goodResidue a q := by
    intro a
    by_cases h : goodResidue a q
    · rw [ite_eq_left h]
      have htrue : (R + 1) % 2 = 0 := by omega
      simp [htrue, h]
    · rw [ite_eq_right h]
      simp [hR, h]
  have hsum : (∑ a ∈ (q ^ (4 * m)).divisors,
        (if ¬(R + (if goodResidue a q then 1 else 0)) % 2 = 0 then a.factorization q
          else 0))
      = ∑ a ∈ (q ^ (4 * m)).divisors.filter (fun a => ¬goodResidue a q),
        a.factorization q := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    simp only [hiff a]
  exact hsum.trans (sum_filter_not_good_prime_pow q m hq)

private def splitSet (S : ℕ) : Finset ℕ :=
  (S ^ 4).divisors.filter fun d =>
    (((S ^ 4).primeFactors.filter (goodResidue d)).card % 2 = 0)

private theorem splitSet_subset (S : ℕ) : splitSet S ⊆ (S ^ 4).divisors :=
  Finset.filter_subset _ _

private theorem sum_factorization_off_support (S p : ℕ) (hS : S ≠ 0)
    (hmem : p ∉ (S ^ 4).primeFactors) :
    ∑ d ∈ splitSet S, d.factorization p
      = ∑ d ∈ (S ^ 4).divisors \ splitSet S, d.factorization p := by
  have hT0 : S ^ 4 ≠ 0 := pow_ne_zero 4 hS
  have hall : ∀ d ∈ (S ^ 4).divisors, d.factorization p = 0 := by
    intro d hd
    by_cases hp : p.Prime
    · have hndvdT : ¬ p ∣ S ^ 4 :=
        fun h => hmem (Nat.mem_primeFactors.mpr ⟨hp, h, hT0⟩)
      have hndvd : ¬ p ∣ d :=
        fun h => hndvdT (h.trans (Nat.dvd_of_mem_divisors hd))
      exact Nat.factorization_eq_zero_of_not_dvd hndvd
    · exact Nat.factorization_eq_zero_of_not_prime _ hp
  have h1 : (∑ d ∈ splitSet S, d.factorization p) = 0 :=
    Finset.sum_eq_zero fun d hd => hall d (splitSet_subset S hd)
  have h2 : (∑ d ∈ (S ^ 4).divisors \ splitSet S, d.factorization p) = 0 :=
    Finset.sum_eq_zero fun d hd => hall d (Finset.mem_sdiff.mp hd).1
  rw [h1, h2]

private theorem primeFactors_insert_ordCompl (S q : ℕ) (hS : S ≠ 0)
    (hmem : q ∈ (S ^ 4).primeFactors) :
    (S ^ 4).primeFactors
      = insert q (((S ^ 4) / q ^ (S ^ 4).factorization q).primeFactors) := by
  have hT0 : S ^ 4 ≠ 0 := pow_ne_zero 4 hS
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hmem
  have hqdvdT : q ∣ S ^ 4 := Nat.dvd_of_mem_primeFactors hmem
  have hM0 : (S ^ 4) / q ^ (S ^ 4).factorization q ≠ 0 := by
    intro h0
    have hQM := Nat.ordProj_mul_ordCompl_eq_self (S ^ 4) q
    rw [h0, mul_zero] at hQM
    exact hT0 hQM.symm
  ext r
  simp only [Finset.mem_insert, Nat.mem_primeFactors]
  constructor
  · intro hcon
    obtain ⟨hr, hrdvd, -⟩ := hcon
    by_cases heq : r = q
    · exact Or.inl heq
    · refine Or.inr ⟨hr, ?_, hM0⟩
      have hQM := Nat.ordProj_mul_ordCompl_eq_self (S ^ 4) q
      have hrdiv : r ∣ q ^ (S ^ 4).factorization q ∨
          r ∣ (S ^ 4) / q ^ (S ^ 4).factorization q := by
        have h := hrdvd
        rw [← hQM] at h
        exact (hr.prime.dvd_mul).mp h
      rcases hrdiv with hQ | hM
      · exfalso
        have hrq : r ∣ q := hr.dvd_of_dvd_pow hQ
        have heq2 : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp hrq
        exact heq heq2
      · exact hM
  · intro hcon
    rcases hcon with rfl | ⟨hr, hrm, -⟩
    · exact ⟨hq, hqdvdT, hT0⟩
    · refine ⟨hr, ?_, hT0⟩
      exact hrm.trans (Nat.ordCompl_dvd (S ^ 4) q)

private theorem sum_factorization_mem_primeFactors (S q : ℕ) (hS : S ≠ 0)
    (hmem : q ∈ (S ^ 4).primeFactors) :
    ∑ d ∈ splitSet S, d.factorization q
      = ∑ d ∈ (S ^ 4).divisors \ splitSet S, d.factorization q := by
  have hT0 : S ^ 4 ≠ 0 := pow_ne_zero 4 hS
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hmem
  have hβ : (S ^ 4).factorization q = 4 * S.factorization q := by
    rw [Nat.factorization_pow]
    simp [Finsupp.smul_apply]
  set m : ℕ := S.factorization q with hm
  set Q : ℕ := q ^ (S ^ 4).factorization q with hQ
  set M : ℕ := (S ^ 4) / q ^ (S ^ 4).factorization q with hM
  have hQM : Q * M = S ^ 4 := Nat.ordProj_mul_ordCompl_eq_self (S ^ 4) q
  have hQ0 : Q ≠ 0 := by rw [hQ]; exact pow_ne_zero _ hq.ne_zero
  have hM0 : M ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hQM
    exact hT0 hQM.symm
  have hcop : Q.Coprime M :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hq hT0)
  have hqdvdM : ¬ q ∣ M := Nat.not_dvd_ordCompl hq hT0
  have hQ4 : Q = q ^ (4 * m) := by rw [hQ, hβ]
  have hP : (S ^ 4).primeFactors = insert q M.primeFactors :=
    primeFactors_insert_ordCompl S q hS hmem
  have hqMpf : q ∉ M.primeFactors := by
    intro hcon
    exact hqdvdM (Nat.dvd_of_mem_primeFactors hcon)
  have hfactmul : ∀ a ∈ Q.divisors, ∀ b ∈ M.divisors,
      (a * b).factorization q = a.factorization q := by
    intro a ha b hb
    have ha0 : a ≠ 0 := (Nat.pos_of_mem_divisors ha).ne'
    have hb0 : b ≠ 0 := (Nat.pos_of_mem_divisors hb).ne'
    have hbq : b.factorization q = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hcon =>
        hqdvdM (hcon.trans (Nat.dvd_of_mem_divisors hb))
    have hmul := congrArg (fun f : ℕ →₀ ℕ => f q) (Nat.factorization_mul ha0 hb0)
    simp only [Finsupp.add_apply, hbq, add_zero] at hmul
    exact hmul
  have hfactmul' : ∀ a ∈ Q.divisors, ∀ b ∈ M.divisors, ∀ r ∈ M.primeFactors,
      (a * b).factorization r = b.factorization r := by
    intro a ha b hb r hr
    have ha0 : a ≠ 0 := (Nat.pos_of_mem_divisors ha).ne'
    have hb0 : b ≠ 0 := (Nat.pos_of_mem_divisors hb).ne'
    have har : a.factorization r = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hcon
      have hrdvdQ : r ∣ Q := hcon.trans (Nat.dvd_of_mem_divisors ha)
      rw [hQ] at hrdvdQ
      have hrprime : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrq : r ∣ q := hrprime.dvd_of_dvd_pow hrdvdQ
      have heq : r = q := (Nat.prime_dvd_prime_iff_eq hrprime hq).mp hrq
      rw [heq] at hr
      exact hqMpf hr
    have hmul := congrArg (fun f : ℕ →₀ ℕ => f r) (Nat.factorization_mul ha0 hb0)
    simp only [Finsupp.add_apply, har, zero_add] at hmul
    exact hmul
  have hcnt : ∀ a ∈ Q.divisors, ∀ b ∈ M.divisors,
      (((S ^ 4).primeFactors.filter (goodResidue (a * b))).card
        = ((M.primeFactors.filter (goodResidue b)).card
          + (if goodResidue a q then 1 else 0))) := by
    intro a ha b hb
    have hqgood : goodResidue (a * b) q ↔ goodResidue a q := by
      simp only [goodResidue, hfactmul a ha b hb]
    have hrest : (M.primeFactors.filter (goodResidue (a * b)))
        = M.primeFactors.filter (goodResidue b) := by
      apply Finset.filter_congr
      intro r hr
      simp only [goodResidue, hfactmul' a ha b hb r hr]
    rw [hP, Finset.filter_insert, hrest]
    by_cases hqa : goodResidue a q
    · have hnotmem : q ∉ M.primeFactors.filter (goodResidue b) :=
        fun hcon => hqMpf (Finset.mem_filter.mp hcon).1
      rw [ite_eq_left (hqgood.mpr hqa), ite_eq_left hqa,
        Finset.card_insert_of_notMem hnotmem]
    · rw [ite_eq_right (fun h => hqa (hqgood.mp h)), ite_eq_right hqa, add_zero]
  have hdiv : (S ^ 4).divisors
      = Finset.image (fun p => p.1 * p.2) (Q.divisors ×ˢ M.divisors) := by
    rw [← hQM, Nat.divisors_mul, Finset.mul_def]
  have hsum2 : ∀ g : ℕ → ℕ, (∑ d ∈ (S ^ 4).divisors, g d)
      = ∑ b ∈ M.divisors, ∑ a ∈ Q.divisors, g (a * b) := by
    intro g
    rw [hdiv, Finset.sum_image hcop.mul_injOn_divisors, Finset.sum_product,
      Finset.sum_comm]
  have hsplit : splitSet S = (S ^ 4).divisors.filter
      (fun d => ((S ^ 4).primeFactors.filter (goodResidue d)).card % 2 = 0) := rfl
  have hA_eq : (∑ d ∈ splitSet S, d.factorization q)
      = ∑ b ∈ M.divisors, ∑ a ∈ Q.divisors,
        (if ((M.primeFactors.filter (goodResidue b)).card
            + (if goodResidue a q then 1 else 0)) % 2 = 0 then a.factorization q
          else 0) := by
    rw [hsplit, Finset.sum_filter, hsum2]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro a ha
    simp only [hfactmul a ha b hb, hcnt a ha b hb]
  have hsdiff : (S ^ 4).divisors \ splitSet S = (S ^ 4).divisors.filter
      (fun d => ¬((S ^ 4).primeFactors.filter (goodResidue d)).card % 2 = 0) := by
    rw [hsplit]
    ext d
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    by_cases hd : d ∈ (S ^ 4).divisors <;> simp [hd]
  have hC_eq : (∑ d ∈ (S ^ 4).divisors \ splitSet S, d.factorization q)
      = ∑ b ∈ M.divisors, ∑ a ∈ Q.divisors,
        (if ¬((M.primeFactors.filter (goodResidue b)).card
            + (if goodResidue a q then 1 else 0)) % 2 = 0 then a.factorization q
          else 0) := by
    rw [hsdiff, Finset.sum_filter, hsum2]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro a ha
    simp only [hfactmul a ha b hb, hcnt a ha b hb]
  rw [hA_eq, hC_eq, hQ4]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hER : Even ((M.primeFactors.filter (goodResidue b)).card)
  · have hR : ((M.primeFactors.filter (goodResidue b)).card) % 2 = 0 :=
      Nat.even_iff.mp hER
    rw [inner_sum_even_pos q m _ hq hR, inner_sum_even_neg q m _ hq hR]
  · have hO : Odd ((M.primeFactors.filter (goodResidue b)).card) :=
      (Nat.even_or_odd _).resolve_left hER
    have hR : ((M.primeFactors.filter (goodResidue b)).card) % 2 = 1 :=
      Nat.odd_iff.mp hO
    rw [inner_sum_odd_pos q m _ hq hR, inner_sum_odd_neg q m _ hq hR]

private theorem exists_split_fourth_pow (S : ℕ) :
    ∃ A : Finset ℕ, A ⊆ (S ^ 4).divisors ∧
      (∏ d ∈ A, d) = ∏ d ∈ (S ^ 4).divisors \ A, d := by
  by_cases hS : S = 0
  · subst hS
    refine ⟨∅, Finset.empty_subset _, ?_⟩
    simp
  · refine ⟨splitSet S, splitSet_subset S, ?_⟩
    have hA0 : (∏ d ∈ splitSet S, d) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun d hd =>
        (Nat.pos_of_mem_divisors (splitSet_subset S hd)).ne'
    have hC0 : (∏ d ∈ (S ^ 4).divisors \ splitSet S, d) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun d hd =>
        (Nat.pos_of_mem_divisors (Finset.mem_sdiff.mp hd).1).ne'
    apply Nat.eq_of_factorization_eq hA0 hC0
    intro p
    rw [Nat.factorization_prod_apply
      (fun d hd => (Nat.pos_of_mem_divisors (splitSet_subset S hd)).ne'),
      Nat.factorization_prod_apply
      (fun d hd => (Nat.pos_of_mem_divisors (Finset.mem_sdiff.mp hd).1).ne')]
    by_cases hmem : p ∈ (S ^ 4).primeFactors
    · exact sum_factorization_mem_primeFactors S p hS hmem
    · exact sum_factorization_off_support S p hS hmem

/-- **$k$-m-perfect numbers with $k$ a positive multiple of $4$ are super-m-Zumkeller.** Let
$k \ge 2$ be a natural number with $k \equiv 0 \pmod 4$. Then every natural number that is
$k$-m-perfect is super-m-Zumkeller.

Source: Harish Patodia, "Super m-Zumkeller Numbers", Theorem 6. -/
theorem isSuperMZumkeller_of_isKMPerfect (k n : ℕ)
    (hk : 2 ≤ k) (hk4 : k % 4 = 0) (h : IsKMPerfect k n) :
    IsSuperMZumkeller n := by
  unfold IsKMPerfect at h
  unfold IsSuperMZumkeller
  by_cases hn : n = 0
  · subst hn
    simp only [divisorProd, Nat.divisors_zero, Finset.prod_empty] at h
    rw [zero_pow (by omega : k ≠ 0)] at h
    exact False.elim (one_ne_zero h)
  · have hk4' : k = 4 * (k / 4) := by omega
    have hpow : n ^ k = (n ^ (k / 4)) ^ 4 := by
      conv_lhs => rw [hk4']
      rw [mul_comm, pow_mul]
    rw [h, hpow]
    exact exists_split_fourth_pow (n ^ (k / 4))

end MathlibExt.NumberTheory.SuperMZumkellerWanted
