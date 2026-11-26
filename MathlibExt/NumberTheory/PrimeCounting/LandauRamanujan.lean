/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Order.Floor.Semifield

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.SumTwoSquares
import MathlibExt.NumberTheory.PrimeCounting.ModFourMeanValue

namespace MetaMathlibExt

open Asymptotics Filter Finset Nat Chebyshev ArithmeticFunction
open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Indicator of positive integers with no prime factor `≡ 3 mod 4`. -/
private noncomputable def lrH (n : ℕ) : ℝ :=
  if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 ≠ 3 then 1 else 0

/-- Indicator of positive integers all of whose prime factors are `≡ 3 mod 4`. -/
private noncomputable def lrG (k : ℕ) : ℝ :=
  if k ≠ 0 ∧ ∀ p ∈ k.primeFactors, p % 4 = 3 then 1 else 0

private lemma lrH_zero : lrH 0 = 0 := by simp [lrH]

private lemma lrG_zero : lrG 0 = 0 := by simp [lrG]

private lemma lrH_one : lrH 1 = 1 := by simp [lrH]

private lemma lrG_one : lrG 1 = 1 := by simp [lrG]

private lemma lrH_nonneg (n : ℕ) : 0 ≤ lrH n := by
  unfold lrH
  split_ifs <;> norm_num

private lemma lrH_le_one (n : ℕ) : lrH n ≤ 1 := by
  unfold lrH
  split_ifs <;> norm_num

private lemma lrG_nonneg (k : ℕ) : 0 ≤ lrG k := by
  unfold lrG
  split_ifs <;> norm_num

private lemma lrG_le_one (k : ℕ) : lrG k ≤ 1 := by
  unfold lrG
  split_ifs <;> norm_num

private lemma lrH_mul (m n : ℕ) : lrH (m * n) = lrH m * lrH n := by
  by_cases hm : m = 0
  · subst hm
    simp [lrH_zero]
  · by_cases hn : n = 0
    · subst hn
      simp [lrH_zero]
    · have hU : (m * n).primeFactors = m.primeFactors ∪ n.primeFactors :=
        Nat.primeFactors_mul hm hn
      have hIff : (m * n ≠ 0 ∧ ∀ p ∈ (m * n).primeFactors, p % 4 ≠ 3) ↔
          (m ≠ 0 ∧ ∀ p ∈ m.primeFactors, p % 4 ≠ 3) ∧
          (n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 ≠ 3) := by
        rw [hU]
        constructor
        · rintro ⟨_, hH⟩
          exact ⟨⟨hm, fun p hp => hH p (Finset.mem_union.mpr (Or.inl hp))⟩,
            ⟨hn, fun p hp => hH p (Finset.mem_union.mpr (Or.inr hp))⟩⟩
        · rintro ⟨⟨hm', hHm⟩, ⟨hn', hHn⟩⟩
          refine ⟨mul_ne_zero hm' hn', fun p hp => ?_⟩
          rcases Finset.mem_union.mp hp with h | h
          · exact hHm p h
          · exact hHn p h
      simp only [lrH, hIff]
      split_ifs with h1 h2 h3 <;> simp_all

/-- `H(x)`: count of `n ≤ x` with `lrH n = 1`. -/
private noncomputable def lrCount (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n

private lemma lrCount_nonneg (x : ℝ) : 0 ≤ lrCount x :=
  Finset.sum_nonneg fun n _ => lrH_nonneg n

private lemma lrCount_le {y : ℝ} (hy : 0 ≤ y) : lrCount y ≤ y := by
  calc lrCount y = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, lrH n := rfl
    _ ≤ ∑ _n ∈ Finset.Ioc 0 ⌊y⌋₊, (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => lrH_le_one n
    _ = (⌊y⌋₊ : ℝ) := by simp [Finset.sum_const, Nat.card_Ioc]
    _ ≤ y := Nat.floor_le hy

/-- `lrH` on a prime is determined by the residue of the prime mod 4. -/
private lemma lrH_prime_eq {p : ℕ} (hp : p.Prime) :
    lrH p = if p % 4 = 3 then 0 else 1 := by
  simp [lrH, hp.ne_zero, hp.primeFactors, ite_not]

/-- `B(x)`: the `k`-sum in the two-squares decomposition. -/
private noncomputable def lrB (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, lrG k * lrCount (x / (k : ℝ) ^ 2)

/-- `lrH n = 1` unfolds to the defining condition. -/
private lemma lrH_eq_one {n : ℕ} :
    lrH n = 1 ↔ n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 ≠ 3 := by
  unfold lrH
  by_cases h : n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 ≠ 3 <;> simp [h]

/-- `lrG k = 1` unfolds to the defining condition. -/
private lemma lrG_eq_one {k : ℕ} :
    lrG k = 1 ↔ k ≠ 0 ∧ ∀ p ∈ k.primeFactors, p % 4 = 3 := by
  unfold lrG
  by_cases h : k ≠ 0 ∧ ∀ p ∈ k.primeFactors, p % 4 = 3 <;> simp [h]

/-- `lrH` takes only the values `0` and `1`. -/
private lemma lrH_01 (n : ℕ) : lrH n = 0 ∨ lrH n = 1 := by
  unfold lrH
  split_ifs <;> simp

/-- `lrG` takes only the values `0` and `1`. -/
private lemma lrG_01 (k : ℕ) : lrG k = 0 ∨ lrG k = 1 := by
  unfold lrG
  split_ifs <;> simp

/-- A product `k ^ 2 * m` with `lrH m = 1` is a sum of two squares
(the `k ^ 2` part always contributes even valuations). -/
private lemma lr_sq_mul_mem {k m : ℕ} (hk0 : k ≠ 0) (hm0 : m ≠ 0)
    (hm : lrH m = 1) :
    ∃ a b : ℕ, k ^ 2 * m = a ^ 2 + b ^ 2 := by
  rw [Nat.eq_sq_add_sq_iff]
  intro q hq hq3
  have hqP : q.Prime := Nat.prime_of_mem_primeFactors hq
  have : Fact q.Prime := ⟨hqP⟩
  have hqm : ¬ q ∣ m := by
    intro hdvd
    have hmem : q ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hqP, hdvd, hm0⟩
    exact (lrH_eq_one.mp hm).2 q hmem hq3
  have h1 : multiplicity q m = 0 := multiplicity_eq_zero_of_not_dvd hqm
  have h2 : multiplicity q (k ^ 2 * m) = 2 * multiplicity q k := by
    rw [Nat.multiplicity_mul (pow_ne_zero 2 hk0) hm0, Nat.multiplicity_pow, h1, add_zero]
  rw [Nat.padicValNat_def, h2]
  exact ⟨multiplicity q k, by ring⟩

/-- Uniqueness of the `k ^ 2 * m` decomposition. -/
private lemma lr_sq_mul_inj {k m k' m' : ℕ} (hk0 : k ≠ 0) (hm0 : m ≠ 0)
    (hk0' : k' ≠ 0) (hm0' : m' ≠ 0)
    (hk : lrG k = 1) (hm : lrH m = 1) (hk' : lrG k' = 1) (hm' : lrH m' = 1)
    (h : k ^ 2 * m = k' ^ 2 * m') : k = k' ∧ m = m' := by
  have hkk : k = k' := by
    apply Nat.eq_of_factorization_eq hk0 hk0'
    intro p
    by_cases hpP : p.Prime
    · have : Fact p.Prime := ⟨hpP⟩
      have hval : multiplicity p (k ^ 2 * m) = multiplicity p (k' ^ 2 * m') := by
        rw [h]
      rw [Nat.multiplicity_mul (pow_ne_zero 2 hk0) hm0, Nat.multiplicity_pow,
        Nat.multiplicity_mul (pow_ne_zero 2 hk0') hm0', Nat.multiplicity_pow] at hval
      by_cases hp3 : p % 4 = 3
      · have hvm : multiplicity p m = 0 := by
          apply multiplicity_eq_zero_of_not_dvd
          intro hdvd
          have hmem : p ∈ m.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hpP, hdvd, hm0⟩
          exact (lrH_eq_one.mp hm).2 p hmem hp3
        have hvm' : multiplicity p m' = 0 := by
          apply multiplicity_eq_zero_of_not_dvd
          intro hdvd
          have hmem : p ∈ m'.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hpP, hdvd, hm0'⟩
          exact (lrH_eq_one.mp hm').2 p hmem hp3
        have hkk2 : multiplicity p k = multiplicity p k' := by omega
        rw [Nat.factorization_def _ hpP, Nat.factorization_def _ hpP, hkk2]
      · have hvk : multiplicity p k = 0 := by
          apply multiplicity_eq_zero_of_not_dvd
          intro hdvd
          have hmem : p ∈ k.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hpP, hdvd, hk0⟩
          exact hp3 ((lrG_eq_one.mp hk).2 p hmem)
        have hvk' : multiplicity p k' = 0 := by
          apply multiplicity_eq_zero_of_not_dvd
          intro hdvd
          have hmem : p ∈ k'.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hpP, hdvd, hk0'⟩
          exact hp3 ((lrG_eq_one.mp hk').2 p hmem)
        rw [Nat.factorization_def _ hpP, Nat.factorization_def _ hpP, hvk, hvk']
    · rw [Nat.factorization_eq_zero_of_not_prime _ hpP,
        Nat.factorization_eq_zero_of_not_prime _ hpP]
  refine ⟨hkk, ?_⟩
  rw [hkk] at h
  exact mul_left_cancel₀ (pow_ne_zero 2 hk0') h

/-- Every positive sum of two squares splits as `k ^ 2 * m` with `lrG k = lrH m = 1`. -/
private lemma lr_exists_sq_mul {n : ℕ} (hn1 : 1 ≤ n)
    (hsq : ∃ a b : ℕ, n = a ^ 2 + b ^ 2) :
    ∃ k m : ℕ, 1 ≤ k ∧ 1 ≤ m ∧ lrG k = 1 ∧ lrH m = 1 ∧ k ^ 2 * m = n := by
  have hn0 : n ≠ 0 := by omega
  have hchar := Nat.eq_sq_add_sq_iff.mp hsq
  set S : Finset ℕ := n.primeFactors.filter (fun p => p % 4 = 3) with hSdef
  set k : ℕ := ∏ p ∈ S, p ^ (n.factorization p / 2) with hkdef
  have hmemS : ∀ p ∈ S, p.Prime ∧ p % 4 = 3 := by
    intro p hp
    have hpf : p ∈ n.primeFactors := Finset.mem_of_mem_filter p hp
    exact ⟨Nat.prime_of_mem_primeFactors hpf, (Finset.mem_filter.mp hp).2⟩
  have heven : ∀ p ∈ S, Even (n.factorization p) := by
    intro p hp
    have hpf : p ∈ n.primeFactors := Finset.mem_of_mem_filter p hp
    have hpp := (hmemS p hp).1
    rw [Nat.factorization_def n hpp, ← Nat.padicValNat_def]
    exact hchar p hpf (hmemS p hp).2
  have hksq : k ^ 2 = ∏ p ∈ S, p ^ (n.factorization p) := by
    rw [hkdef, pow_two, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    obtain ⟨t, ht⟩ := heven p hp
    have hv2 : n.factorization p / 2 = t := by omega
    rw [hv2, ← pow_add, ← ht]
  have hprod_eq : ∏ p ∈ n.primeFactors, p ^ (n.factorization p) = n := by
    have h := Nat.prod_factorization_pow_eq_self hn0
    rwa [Nat.prod_factorization_eq_prod_primeFactors] at h
  have hdvd : k ^ 2 ∣ n := by
    have hsub : S ⊆ n.primeFactors := Finset.filter_subset _ _
    have h := Finset.prod_sdiff hsub (f := fun p => p ^ (n.factorization p))
    rw [mul_comm] at h
    have h2 : k ^ 2 ∣ ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
      rw [hksq]
      exact ⟨∏ x ∈ n.primeFactors \ S, x ^ (n.factorization x), h.symm⟩
    rwa [hprod_eq] at h2
  obtain ⟨m, hm⟩ := hdvd
  have hk0 : k ≠ 0 := by
    rw [hkdef]
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hpp := (hmemS p hp).1
    exact pow_ne_zero _ (ne_of_gt hpp.pos)
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  have hkm_eq : k ^ 2 * m = n := hm.symm
  have hm0 : m ≠ 0 := by
    intro hcon
    apply hn0
    calc n = k ^ 2 * m := hm
      _ = 0 := by rw [hcon, mul_zero]
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
  have hGk : lrG k = 1 := by
    rw [lrG_eq_one]
    refine ⟨hk0, fun q hq => ?_⟩
    have hqP : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqdvd : q ∣ k := Nat.dvd_of_mem_primeFactors hq
    rw [hkdef] at hqdvd
    obtain ⟨p, hpS, hqp⟩ :=
      (Nat.prime_iff.mp hqP).dvd_finsetProd_iff _ |>.mp hqdvd
    have hqp2 : q ∣ p := hqP.dvd_of_dvd_pow hqp
    have hpP : p.Prime := (hmemS p hpS).1
    have hqp3 : q = p := (Nat.prime_dvd_prime_iff_eq hqP hpP).mp hqp2
    rw [hqp3]
    exact (hmemS p hpS).2
  have hHm : lrH m = 1 := by
    rw [lrH_eq_one]
    refine ⟨hm0, fun q hq => ?_⟩
    have hqP : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqdvd : q ∣ m := Nat.dvd_of_mem_primeFactors hq
    intro hq3
    have hmn : m ∣ n := by
      have h := dvd_mul_left m (k ^ 2)
      rwa [hkm_eq] at h
    have hqn : q ∣ n := dvd_trans hqdvd hmn
    have hmem_n : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hqP, hqn, hn0⟩
    have hqS : q ∈ S := Finset.mem_filter.mpr ⟨hmem_n, hq3⟩
    have hpow_dvd_k2 : q ^ (n.factorization q) ∣ k ^ 2 := by
      rw [hksq]
      exact Finset.dvd_prod_of_mem _ hqS
    have hpow_dvd_m : q ^ (m.factorization q) ∣ m := Nat.ordProj_dvd m q
    have hmul_dvd : q ^ (n.factorization q) * q ^ (m.factorization q) ∣ k ^ 2 * m :=
      mul_dvd_mul hpow_dvd_k2 hpow_dvd_m
    rw [hkm_eq] at hmul_dvd
    rw [← pow_add] at hmul_dvd
    have hle : n.factorization q + m.factorization q ≤ n.factorization q :=
      (Nat.Prime.pow_dvd_iff_le_factorization hqP hn0).mp hmul_dvd
    have hposv : 1 ≤ m.factorization q := by
      have hqdvd1 : q ^ 1 ∣ m := by rwa [pow_one]
      exact (Nat.Prime.pow_dvd_iff_le_factorization hqP hm0).mp hqdvd1
    omega
  exact ⟨k, m, hk1, hm1, hGk, hHm, hkm_eq⟩

/-- Decomposition of the two-squares count: the number of `n ≤ x`, `n ≥ 1`,
that are a sum of two squares equals `B(x)`. -/
private lemma lr_twoSq_count_eq {x : ℝ} (hx : 0 ≤ x) :
    ((Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
      (Finset.Ioc 0 ⌊x⌋₊)).card : ℝ) = lrB x := by
  classical
  set T : Finset (Σ _ : ℕ, ℕ) := (Finset.Ioc 0 ⌊x⌋₊).sigma
    (fun k => (Finset.Ioc 0 ⌊x⌋₊).filter
      (fun m => lrG k = 1 ∧ lrH m = 1 ∧ k ^ 2 * m ≤ ⌊x⌋₊)) with hTdef
  have himg : Finset.image (fun p : Σ _ : ℕ, ℕ => p.1 ^ 2 * p.2) T
      = Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
        (Finset.Ioc 0 ⌊x⌋₊) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨k, m⟩, hkm, rfl⟩
      obtain ⟨hkI, hmF⟩ := Finset.mem_sigma.mp hkm
      obtain ⟨hmI, hGk, hHm, hle⟩ := Finset.mem_filter.mp hmF
      obtain ⟨hk0, hkN⟩ := Finset.mem_Ioc.mp hkI
      obtain ⟨hm0, hmN⟩ := Finset.mem_Ioc.mp hmI
      have hk0k : 0 < k := hk0
      have hm0m : 0 < m := hm0
      have hpos : 0 < k ^ 2 * m :=
        Nat.mul_pos (pow_pos hk0k 2) hm0m
      refine ⟨Finset.mem_Ioc.mpr ⟨hpos, hle⟩,
        lr_sq_mul_mem (ne_of_gt hk0k) (ne_of_gt hm0m) hHm⟩
    · rintro ⟨hnI, hsq⟩
      obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.mp hnI
      obtain ⟨k, m, hk1, hm1, hGk, hHm, hkm⟩ := lr_exists_sq_mul hn0 hsq
      have hpos : 0 < k ^ 2 * m := by
        rw [hkm]
        omega
      have hk_le : k ≤ k ^ 2 * m :=
        Nat.le_of_dvd hpos ⟨k * m, by ring⟩
      have hm_le : m ≤ k ^ 2 * m :=
        Nat.le_of_dvd hpos ⟨k ^ 2, by ring⟩
      refine ⟨⟨k, m⟩, ?_, hkm⟩
      rw [hTdef]
      refine Finset.mem_sigma.mpr ⟨Finset.mem_Ioc.mpr ⟨hk1, ?_⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hm1, ?_⟩, hGk, hHm, ?_⟩⟩
      · exact le_trans hk_le (hkm ▸ hnN)
      · exact le_trans hm_le (hkm ▸ hnN)
      · rw [hkm]
        exact hnN
  have hinj : Set.InjOn (fun p : Σ _ : ℕ, ℕ => p.1 ^ 2 * p.2) (↑T) := by
    intro a ha b hb hab
    obtain ⟨k, m⟩ := a
    obtain ⟨k', m'⟩ := b
    have ha' := Finset.mem_coe.mp ha
    have hb' := Finset.mem_coe.mp hb
    obtain ⟨hkI, hmF⟩ := Finset.mem_sigma.mp ha'
    obtain ⟨hmI, hGk, hHm, -⟩ := Finset.mem_filter.mp hmF
    obtain ⟨hkI', hmF'⟩ := Finset.mem_sigma.mp hb'
    obtain ⟨hmI', hGk', hHm', -⟩ := Finset.mem_filter.mp hmF'
    have hk0k : 0 < k := (Finset.mem_Ioc.mp hkI).1
    have hm0m : 0 < m := (Finset.mem_Ioc.mp hmI).1
    have hk0k' : 0 < k' := (Finset.mem_Ioc.mp hkI').1
    have hm0m' : 0 < m' := (Finset.mem_Ioc.mp hmI').1
    have hab' : k ^ 2 * m = k' ^ 2 * m' := hab
    have hk0n : k ≠ 0 := ne_of_gt hk0k
    have hm0n : m ≠ 0 := ne_of_gt hm0m
    have hk0n' : k' ≠ 0 := ne_of_gt hk0k'
    have hm0n' : m' ≠ 0 := ne_of_gt hm0m'
    obtain ⟨hkk, hmm⟩ :=
      lr_sq_mul_inj hk0n hm0n hk0n' hm0n' hGk hHm hGk' hHm' hab'
    subst hkk
    subst hmm
    rfl
  have hcardT : (T.card : ℝ) = lrB x := by
    have hsigma : T.card = ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊,
        ((Finset.Ioc 0 ⌊x⌋₊).filter
          (fun m => lrG k = 1 ∧ lrH m = 1 ∧ k ^ 2 * m ≤ ⌊x⌋₊)).card := by
      rw [hTdef]
      exact Finset.card_sigma _ _
    have hlrB : lrB x
        = ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, lrG k * lrCount (x / (k : ℝ) ^ 2) := rfl
    rw [hsigma, Nat.cast_sum, hlrB]
    apply Finset.sum_congr rfl
    intro k hkI
    have hk1 : 1 ≤ k := (Finset.mem_Ioc.mp hkI).1
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk1
    have hcast : ∀ m : ℕ, ((k ^ 2 * m : ℕ) : ℝ) = (k : ℝ) ^ 2 * (m : ℝ) := by
      intro m
      push_cast
      ring
    by_cases hGk : lrG k = 1
    · have hfib : (Finset.Ioc 0 ⌊x⌋₊).filter
          (fun m => lrG k = 1 ∧ lrH m = 1 ∧ k ^ 2 * m ≤ ⌊x⌋₊)
          = (Finset.Ioc 0 ⌊x / (k : ℝ) ^ 2⌋₊).filter (fun m => lrH m = 1) := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨hm0, hmN⟩, -, hHm, hle⟩
          have hleR : (k : ℝ) ^ 2 * (m : ℝ) ≤ x := by
            have h1 : ((k ^ 2 * m : ℕ) : ℝ) ≤ x :=
              le_trans (by exact_mod_cast hle) (Nat.floor_le hx)
            rwa [hcast] at h1
          have hmk : (m : ℝ) ≤ x / (k : ℝ) ^ 2 := by
            rw [le_div_iff₀ (pow_pos hkpos 2)]
            linear_combination hleR
          exact ⟨⟨hm0, Nat.le_floor hmk⟩, hHm⟩
        · rintro ⟨⟨hm0, hmN'⟩, hHm⟩
          have hmk : (m : ℝ) ≤ x / (k : ℝ) ^ 2 :=
            le_trans (by exact_mod_cast hmN')
              (Nat.floor_le (by positivity))
          have hleR : (k : ℝ) ^ 2 * (m : ℝ) ≤ x := by
            have h2 := (le_div_iff₀ (pow_pos hkpos 2)).mp hmk
            linear_combination h2
          have hle : k ^ 2 * m ≤ ⌊x⌋₊ := by
            apply Nat.le_floor
            rw [hcast]
            exact hleR
          have hkk2 : x / (k : ℝ) ^ 2 ≤ x := by
            apply div_le_self hx
            calc (1 : ℝ) = 1 ^ 2 := by norm_num
              _ ≤ (k : ℝ) ^ 2 :=
                pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hk1) 2
          have hmN : m ≤ ⌊x⌋₊ := Nat.le_floor (le_trans hmk hkk2)
          exact ⟨⟨hm0, hmN⟩, hGk, hHm, hle⟩
      rw [hfib]
      have hcard : (((Finset.Ioc 0 ⌊x / (k : ℝ) ^ 2⌋₊).filter
          (fun m => lrH m = 1)).card : ℝ) = lrCount (x / (k : ℝ) ^ 2) := by
        have hlrC : lrCount (x / (k : ℝ) ^ 2)
            = ∑ m ∈ Finset.Ioc 0 ⌊x / (k : ℝ) ^ 2⌋₊, lrH m := rfl
        rw [hlrC, ← Finset.sum_boole]
        apply Finset.sum_congr rfl
        intro m _
        rcases lrH_01 m with h0 | h1
        · simp [h0]
        · simp [h1]
      rw [hcard, hGk, one_mul]
    · have hGk0 : lrG k = 0 := by
        rcases lrG_01 k with h | h
        · exact h
        · exact absurd h hGk
      have hfib_empty : (Finset.Ioc 0 ⌊x⌋₊).filter
          (fun m => lrG k = 1 ∧ lrH m = 1 ∧ k ^ 2 * m ≤ ⌊x⌋₊) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro m _
        simp [hGk0]
      rw [hfib_empty, Finset.card_empty, Nat.cast_zero, hGk0, zero_mul]
  have h1 : (Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
      (Finset.Ioc 0 ⌊x⌋₊)).card = T.card := by
    rw [← himg]
    exact Finset.card_image_of_injOn hinj
  rw [h1]
  exact hcardT

/-- The `Set.ncard` of the Wanted set is one plus the positive count. -/
private lemma lr_ncard_eq {x : ℝ} (hx : 0 ≤ x) :
    Set.ncard {m : ℕ | (m : ℝ) ≤ x ∧ ∃ a b : ℕ, m = a ^ 2 + b ^ 2}
      = (Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
          (Finset.Ioc 0 ⌊x⌋₊)).card + 1 := by
  have hset : {m : ℕ | (m : ℝ) ≤ x ∧ ∃ a b : ℕ, m = a ^ 2 + b ^ 2}
      = ↑(Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
          (Finset.range (⌊x⌋₊ + 1))) := by
    ext m
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range]
    constructor
    · rintro ⟨hmx, hsq⟩
      have hle : m ≤ ⌊x⌋₊ := Nat.le_floor hmx
      exact ⟨by omega, hsq⟩
    · rintro ⟨hm, hsq⟩
      have hle : m ≤ ⌊x⌋₊ := by omega
      have hcast : (m : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hle
      exact ⟨le_trans hcast (Nat.floor_le hx), hsq⟩
  have hsplit : Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
        (Finset.range (⌊x⌋₊ + 1))
      = Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
          (Finset.Ioc 0 ⌊x⌋₊) ∪ {0} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union,
      Finset.mem_Ioc, Finset.mem_singleton]
    constructor
    · rintro ⟨hm, hsq⟩
      by_cases hm0 : m = 0
      · exact Or.inr hm0
      · have hpos : 0 < m := Nat.pos_of_ne_zero hm0
        exact Or.inl ⟨⟨hpos, by omega⟩, hsq⟩
    · rintro (⟨⟨hm0, hmN⟩, hsq⟩ | rfl)
      · exact ⟨by omega, hsq⟩
      · exact ⟨Nat.zero_lt_succ _, 0, 0, by simp⟩
  have hdisj : Disjoint
      (Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
        (Finset.Ioc 0 ⌊x⌋₊)) {0} := by
    rw [Finset.disjoint_left]
    intro m hmI hm0
    rw [Finset.mem_filter, Finset.mem_Ioc] at hmI
    rw [Finset.mem_singleton] at hm0
    omega
  rw [hset, Set.ncard_coe_finset, hsplit,
    Finset.card_union_of_disjoint hdisj, Finset.card_singleton]

/-- `lrCount` vanishes below `1`. -/
private lemma lrCount_eq_zero_of_lt_one {y : ℝ} (hy : y < 1) : lrCount y = 0 := by
  have hfl : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr hy
  simp [lrCount, hfl]

/-- The square-root log ratio `√(log x) / √(log (x / c))` tends to `1`. -/
private lemma lr_sqrt_ratio_tendsto (c : ℝ) (hc : 1 ≤ c) :
    Filter.Tendsto
      (fun x : ℝ => Real.sqrt (Real.log x) / Real.sqrt (Real.log (x / c)))
      Filter.atTop (nhds 1) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hx : Filter.Tendsto (fun x : ℝ => x / c) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const hc0 tendsto_id
  have h0 : Filter.Tendsto (fun x : ℝ => Real.log c / Real.log x)
      Filter.atTop (nhds 0) := by
    have hloginv : Filter.Tendsto (fun x : ℝ => (Real.log x)⁻¹)
        Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have h := Filter.Tendsto.const_mul (Real.log c) hloginv
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards with x
    rw [div_eq_mul_inv]
  have hratio : Filter.Tendsto (fun x : ℝ => Real.log (x / c) / Real.log x)
      Filter.atTop (nhds 1) := by
    have heq : (fun x : ℝ => Real.log (x / c) / Real.log x) =ᶠ[Filter.atTop]
        (fun x : ℝ => 1 - Real.log c / Real.log x) := by
      filter_upwards [Filter.eventually_gt_atTop 1] with x hx1
      have hxpos : (0 : ℝ) < x := lt_trans zero_lt_one hx1
      have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
      rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hc0),
        sub_div, div_self hlogx]
    have h1 : Filter.Tendsto (fun x : ℝ => 1 - Real.log c / Real.log x)
        Filter.atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub h0
    rw [sub_zero] at h1
    exact h1.congr' heq.symm
  have hsqrt : Filter.Tendsto
      (fun x : ℝ => Real.sqrt (Real.log (x / c) / Real.log x))
      Filter.atTop (nhds 1) := by
    have h := (Real.continuous_sqrt.tendsto 1).comp hratio
    rw [Real.sqrt_one] at h
    exact h
  have hinv : Filter.Tendsto
      (fun x : ℝ => (Real.sqrt (Real.log (x / c) / Real.log x))⁻¹)
      Filter.atTop (nhds 1) := by
    have h := Filter.Tendsto.inv₀ hsqrt one_ne_zero
    rwa [inv_one] at h
  refine hinv.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (max 1 c)] with x hxc
  have hx1 : (1 : ℝ) < x := lt_of_le_of_lt (le_max_left _ _) hxc
  have hxc' : c < x := lt_of_le_of_lt (le_max_right _ _) hxc
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hy1 : (1 : ℝ) < x / c := by
    rw [lt_div_iff₀ hc0]
    linarith
  have hlogy : (0 : ℝ) < Real.log (x / c) := Real.log_pos hy1
  rw [Real.sqrt_div hlogy.le, inv_div]

/-- Pointwise limit of the `k`-th summand in the `B`-sum. -/
private lemma lr_f_tendsto (k : ℕ) (hk : 1 ≤ k) (α : ℝ)
    (hH : Filter.Tendsto
      (fun x => lrCount x * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (α / 2))) :
    Filter.Tendsto
      (fun x => lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (lrG k * (α / 2) / (k : ℝ) ^ 2)) := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  set c : ℝ := (k : ℝ) ^ 2 with hc
  have hcc : (0 : ℝ) < c := pow_pos hkpos 2
  have hc1 : (1 : ℝ) ≤ c := by
    rw [hc]
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hkR 2
  have h1 : Filter.Tendsto
      (fun x : ℝ => lrCount (x / c) * Real.sqrt (Real.log (x / c)) / (x / c))
      Filter.atTop (nhds (α / 2)) :=
    hH.comp (Filter.Tendsto.atTop_div_const hcc tendsto_id)
  have h2 := lr_sqrt_ratio_tendsto c hc1
  have hmul : Filter.Tendsto
      (fun x : ℝ => (lrCount (x / c) * Real.sqrt (Real.log (x / c)) / (x / c)) *
        (Real.sqrt (Real.log x) / Real.sqrt (Real.log (x / c))))
      Filter.atTop (nhds ((α / 2) * 1)) :=
    h1.mul h2
  rw [mul_one] at hmul
  have hscale : Filter.Tendsto
      (fun x : ℝ => (lrG k / c) *
        ((lrCount (x / c) * Real.sqrt (Real.log (x / c)) / (x / c)) *
        (Real.sqrt (Real.log x) / Real.sqrt (Real.log (x / c)))))
      Filter.atTop (nhds ((lrG k / c) * (α / 2))) :=
    Filter.Tendsto.const_mul _ hmul
  have e : (lrG k / c) * (α / 2) = lrG k * (α / 2) / c := by ring
  rw [e] at hscale
  refine hscale.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (max 1 c)] with x hxc
  have hx1 : (1 : ℝ) < x := lt_of_le_of_lt (le_max_left _ _) hxc
  have hxc' : c < x := lt_of_le_of_lt (le_max_right _ _) hxc
  have hxpos : (0 : ℝ) < x := by linarith
  have hypos : (0 : ℝ) < x / c := div_pos hxpos hcc
  have hy1 : (1 : ℝ) < x / c := by
    rw [lt_div_iff₀ hcc]
    linarith
  have hlogy : (0 : ℝ) < Real.log (x / c) := Real.log_pos hy1
  have hs2 : Real.sqrt (Real.log (x / c)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hlogy)
  have hyc : (x / c) ≠ 0 := ne_of_gt hypos
  have hxc0 : x ≠ 0 := ne_of_gt hxpos
  have hc0n : c ≠ 0 := ne_of_gt hcc
  field_simp

/-- Uniform bound for `lrCount y · √(log y) / y` over `y ≥ 2`. -/
private lemma lr_count_uniform_bound (α : ℝ) (hα : 0 < α)
    (hH : Filter.Tendsto
      (fun x => lrCount x * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (α / 2))) :
    ∃ D : ℝ, 0 < D ∧
      ∀ y : ℝ, 2 ≤ y → lrCount y * Real.sqrt (Real.log y) / y ≤ D := by
  have h1 : ∀ᶠ y : ℝ in Filter.atTop,
      lrCount y * Real.sqrt (Real.log y) / y < α / 2 + 1 :=
    hH.eventually (Iio_mem_nhds (by linarith))
  rw [Filter.eventually_atTop] at h1
  obtain ⟨Y₁, hY₁⟩ := h1
  set Y₀ : ℝ := max Y₁ 2 with hY₀
  have hY₀ge : (2 : ℝ) ≤ Y₀ := le_max_right _ _
  refine ⟨max (α / 2 + 1) (Real.sqrt (Real.log Y₀)),
    lt_max_of_lt_left (show (0 : ℝ) < α / 2 + 1 by linarith),
    fun y hy => ?_⟩
  rcases le_total y Y₀ with hle | hle
  · have hypos : (0 : ℝ) < y := by linarith
    have hYpos : (0 : ℝ) < Y₀ := by linarith
    have hlog_le : Real.log y ≤ Real.log Y₀ :=
      Real.log_le_log hypos hle
    have hsq_le : Real.sqrt (Real.log y) ≤ Real.sqrt (Real.log Y₀) :=
      Real.sqrt_le_sqrt hlog_le
    have h1 : lrCount y * Real.sqrt (Real.log y)
        ≤ Real.sqrt (Real.log Y₀) * y := by
      calc lrCount y * Real.sqrt (Real.log y)
          ≤ y * Real.sqrt (Real.log y) :=
            mul_le_mul_of_nonneg_right (lrCount_le hypos.le)
              (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt (Real.log Y₀) * y := by
            calc y * Real.sqrt (Real.log y)
                ≤ y * Real.sqrt (Real.log Y₀) :=
                  mul_le_mul_of_nonneg_left hsq_le hypos.le
              _ = Real.sqrt (Real.log Y₀) * y := mul_comm _ _
    have h2 : lrCount y * Real.sqrt (Real.log y) / y
        ≤ Real.sqrt (Real.log Y₀) := by
      rw [div_le_iff₀ hypos]
      linarith [h1]
    exact le_trans h2 (le_max_right _ _)
  · have hY₁le : Y₁ ≤ y := le_trans (le_max_left _ _) hle
    have hlt := hY₁ y hY₁le
    have hle2 : lrCount y * Real.sqrt (Real.log y) / y ≤ α / 2 + 1 := le_of_lt hlt
    exact le_trans hle2 (le_max_left _ _)

/-- Dominating bound for the `k`-th summand in the `B`-sum. -/
private noncomputable def lrBnd (D : ℝ) (k : ℕ) : ℝ :=
  (Real.sqrt 2 * D + 2 * Real.sqrt (Real.log k)) / (k : ℝ) ^ 2

/-- The dominating bound is summable. -/
private lemma lr_bnd_summable (D : ℝ) : Summable (lrBnd D) := by
  have h1 : Summable (fun k : ℕ => (Real.sqrt 2 * D) / (k : ℝ) ^ 2) := by
    have hs : Summable (fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have he : (fun k : ℕ => (Real.sqrt 2 * D) / (k : ℝ) ^ 2)
        = (fun k : ℕ => (Real.sqrt 2 * D) * ((1 : ℝ) / (k : ℝ) ^ 2)) := by
      funext k
      ring
    rw [he]
    exact hs.mul_left _
  have h2 : Summable
      (fun k : ℕ => (2 * Real.sqrt (Real.log k)) / (k : ℝ) ^ 2) := by
    have hs : Summable
        (fun k : ℕ => (2 : ℝ) * (((k : ℝ) ^ ((3 / 2 : ℝ)))⁻¹)) :=
      ((Real.summable_nat_rpow_inv (p := (3 / 2 : ℝ))).mpr
        (by norm_num)).mul_left 2
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hs
    · apply div_nonneg _ (sq_nonneg _)
      apply mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    · by_cases hk0 : k = 0
      · subst hk0
        simp
      · have hkpos : (0 : ℝ) < (k : ℝ) :=
          by exact_mod_cast Nat.pos_of_ne_zero hk0
        have hK : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos hkpos 2
        have hR : (0 : ℝ) < (k : ℝ) ^ ((3 / 2 : ℝ)) :=
          Real.rpow_pos_of_pos hkpos _
        have hsqrt_le : Real.sqrt (Real.log k) ≤ Real.sqrt (k : ℝ) :=
          Real.sqrt_le_sqrt (Real.log_le_self hkpos.le)
        have hkey : Real.sqrt (Real.log k) * (k : ℝ) ^ ((3 / 2 : ℝ))
            ≤ (k : ℝ) ^ 2 := by
          have hle := mul_le_mul_of_nonneg_right hsqrt_le hR.le
          have eR : Real.sqrt (k : ℝ) * (k : ℝ) ^ ((3 / 2 : ℝ))
              = (k : ℝ) ^ 2 := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_add hkpos]
            norm_num [Real.rpow_two]
          rwa [eR] at hle
        have eR2 : (2 : ℝ) * (((k : ℝ) ^ ((3 / 2 : ℝ)))⁻¹)
            = 2 / (k : ℝ) ^ ((3 / 2 : ℝ)) :=
          (div_eq_mul_inv _ _).symm
        rw [eR2, div_le_div_iff₀ hK hR]
        have h2x := mul_le_mul_of_nonneg_left hkey (show (0 : ℝ) ≤ 2 by norm_num)
        linarith [h2x]
  have hsum : Summable (fun k : ℕ => (Real.sqrt 2 * D) / (k : ℝ) ^ 2 +
      (2 * Real.sqrt (Real.log k)) / (k : ℝ) ^ 2) := h1.add h2
  have heq : (fun k : ℕ => (Real.sqrt 2 * D) / (k : ℝ) ^ 2 +
      (2 * Real.sqrt (Real.log k)) / (k : ℝ) ^ 2) = lrBnd D := by
    funext k
    unfold lrBnd
    rw [add_div]
  rw [← heq]
  exact hsum

/-- Domination of the `B`-summands by the summable bound. -/
private lemma lr_B_dominated (D : ℝ)
    (hDb : ∀ y : ℝ, 2 ≤ y → lrCount y * Real.sqrt (Real.log y) / y ≤ D) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ k : ℕ,
      ‖lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x‖
        ≤ lrBnd D k := by
  have hDnn : (0 : ℝ) ≤ D := by
    have h2 := hDb 2 le_rfl
    have hnn : (0 : ℝ) ≤ lrCount 2 * Real.sqrt (Real.log 2) / 2 := by
      apply div_nonneg _ (by norm_num)
      exact mul_nonneg (lrCount_nonneg _) (Real.sqrt_nonneg _)
    linarith
  filter_upwards [Filter.eventually_ge_atTop 16] with x hx
  intro k
  rcases eq_or_ne k 0 with rfl | hk0
  · have hb0 : lrBnd D 0 = 0 := by
      unfold lrBnd
      norm_num
    rw [lrG_zero, hb0]
    simp
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hc0 : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos hkpos 2
    have hxpos : (0 : ℝ) < x := by linarith
    have hnn : (0 : ℝ)
        ≤ lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x := by
      apply div_nonneg _ hxpos.le
      apply mul_nonneg _ (Real.sqrt_nonneg _)
      exact mul_nonneg (lrG_nonneg k) (lrCount_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hlogk_nn : (0 : ℝ) ≤ Real.log k := Real.log_nonneg hkR
    have hb_extra : (0 : ℝ) ≤ 2 * Real.sqrt (Real.log k) :=
      mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    have hb_main : (0 : ℝ) ≤ Real.sqrt 2 * D :=
      mul_nonneg (Real.sqrt_nonneg _) hDnn
    by_cases hcase : (k : ℝ) ^ 2 ≤ Real.sqrt x
    · have hsqrt4 : (4 : ℝ) ≤ Real.sqrt x := by
        have h16 : Real.sqrt 16 ≤ Real.sqrt x :=
          Real.sqrt_le_sqrt (by linarith)
        have e16 : Real.sqrt (16 : ℝ) = 4 := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        rwa [e16] at h16
      have hsqrtx_nn : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg _
      have hy_ge : Real.sqrt x ≤ x / (k : ℝ) ^ 2 := by
        rw [le_div_iff₀ hc0]
        calc Real.sqrt x * (k : ℝ) ^ 2
            ≤ Real.sqrt x * Real.sqrt x :=
              mul_le_mul_of_nonneg_left hcase hsqrtx_nn
          _ = x := Real.mul_self_sqrt (by linarith)
      have hy2 : (2 : ℝ) ≤ x / (k : ℝ) ^ 2 := by linarith
      have hypos : (0 : ℝ) < x / (k : ℝ) ^ 2 := by linarith
      have hD := hDb _ hy2
      have hlogx_pos : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
      have hlogc : Real.log ((k : ℝ) ^ 2) ≤ (1 / 2) * Real.log x := by
        have h1 : Real.log ((k : ℝ) ^ 2) ≤ Real.log (Real.sqrt x) :=
          Real.log_le_log (pow_pos hkpos 2) hcase
        have h2 : Real.log (Real.sqrt x) = (1 / 2) * Real.log x := by
          rw [Real.log_sqrt (by linarith)]
          ring
        linarith
      have hlogy : Real.log (x / (k : ℝ) ^ 2)
          = Real.log x - Real.log ((k : ℝ) ^ 2) :=
        Real.log_div (ne_of_gt hxpos) (ne_of_gt hc0)
      have hlogy_ge : (1 / 2) * Real.log x ≤ Real.log (x / (k : ℝ) ^ 2) := by
        linarith
      have hlogy_pos : (0 : ℝ) < Real.log (x / (k : ℝ) ^ 2) := by linarith
      have hratio : Real.sqrt (Real.log x)
          / Real.sqrt (Real.log (x / (k : ℝ) ^ 2)) ≤ Real.sqrt 2 := by
        have h1 : Real.log x / Real.log (x / (k : ℝ) ^ 2) ≤ 2 := by
          rw [div_le_iff₀ hlogy_pos]
          linarith
        calc Real.sqrt (Real.log x) / Real.sqrt (Real.log (x / (k : ℝ) ^ 2))
            = Real.sqrt (Real.log x / Real.log (x / (k : ℝ) ^ 2)) := by
              rw [Real.sqrt_div hlogx_pos.le]
          _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h1
      have hHle : lrCount (x / (k : ℝ) ^ 2)
          ≤ D * (x / (k : ℝ) ^ 2)
            / Real.sqrt (Real.log (x / (k : ℝ) ^ 2)) := by
        have hspos : (0 : ℝ) < Real.sqrt (Real.log (x / (k : ℝ) ^ 2)) :=
          Real.sqrt_pos.mpr hlogy_pos
        have hD' : lrCount (x / (k : ℝ) ^ 2)
              * Real.sqrt (Real.log (x / (k : ℝ) ^ 2))
            ≤ D * (x / (k : ℝ) ^ 2) :=
          (div_le_iff₀ hypos).mp hD
        rw [le_div_iff₀ hspos]
        exact hD'
      have g1 : lrG k * lrCount (x / (k : ℝ) ^ 2)
          ≤ D * (x / (k : ℝ) ^ 2)
            / Real.sqrt (Real.log (x / (k : ℝ) ^ 2)) := by
        calc lrG k * lrCount (x / (k : ℝ) ^ 2)
            ≤ 1 * lrCount (x / (k : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right (lrG_le_one k) (lrCount_nonneg _)
          _ = lrCount (x / (k : ℝ) ^ 2) := one_mul _
          _ ≤ _ := hHle
      have hspos : (0 : ℝ) < Real.sqrt (Real.log (x / (k : ℝ) ^ 2)) :=
        Real.sqrt_pos.mpr hlogy_pos
      have hxc0 : x ≠ 0 := ne_of_gt hxpos
      have hc0n : (k : ℝ) ^ 2 ≠ 0 := ne_of_gt hc0
      have hs2n : Real.sqrt (Real.log (x / (k : ℝ) ^ 2)) ≠ 0 := ne_of_gt hspos
      calc lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x
          ≤ (D * (x / (k : ℝ) ^ 2)
              / Real.sqrt (Real.log (x / (k : ℝ) ^ 2)))
              * Real.sqrt (Real.log x) / x := by
              apply div_le_div_of_nonneg_right _ hxpos.le
              exact mul_le_mul_of_nonneg_right g1 (Real.sqrt_nonneg _)
        _ = D * (Real.sqrt (Real.log x)
            / Real.sqrt (Real.log (x / (k : ℝ) ^ 2))) / (k : ℝ) ^ 2 := by
              field_simp
        _ ≤ D * Real.sqrt 2 / (k : ℝ) ^ 2 := by
              apply div_le_div_of_nonneg_right _ hc0.le
              exact mul_le_mul_of_nonneg_left hratio hDnn
        _ ≤ lrBnd D k := by
              unfold lrBnd
              apply div_le_div_of_nonneg_right _ hc0.le
              linarith [mul_comm D (Real.sqrt 2)]
    · have hlt : Real.sqrt x < (k : ℝ) ^ 2 := lt_of_not_ge hcase
      have hlogx_pos : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
      have hlog_lt : Real.log x < 4 * Real.log k := by
        have h1 : Real.log (Real.sqrt x) < Real.log ((k : ℝ) ^ 2) :=
          Real.log_lt_log (Real.sqrt_pos.mpr (by linarith)) hlt
        have h2 : Real.log (Real.sqrt x) = Real.log x / 2 :=
          Real.log_sqrt (by linarith)
        have h3 : Real.log ((k : ℝ) ^ 2) = 2 * Real.log (k : ℝ) := by
          rw [Real.log_pow]
          norm_num
        linarith
      have hy_nn : (0 : ℝ) ≤ x / (k : ℝ) ^ 2 := div_nonneg hxpos.le hc0.le
      have hHle : lrCount (x / (k : ℝ) ^ 2) ≤ x / (k : ℝ) ^ 2 :=
        lrCount_le hy_nn
      have hsq_le : Real.sqrt (Real.log x)
          ≤ 2 * Real.sqrt (Real.log k) := by
        have h1 : Real.log x ≤ 4 * Real.log k := le_of_lt hlog_lt
        calc Real.sqrt (Real.log x)
            ≤ Real.sqrt (4 * Real.log k) := Real.sqrt_le_sqrt h1
          _ = 2 * Real.sqrt (Real.log k) := by
              have e4 : Real.sqrt (4 : ℝ) = 2 := by
                rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
                  Real.sqrt_sq (by norm_num)]
              rw [Real.sqrt_mul (by norm_num), e4]
      have hxc0 : x ≠ 0 := ne_of_gt hxpos
      have hc0n : (k : ℝ) ^ 2 ≠ 0 := ne_of_gt hc0
      calc lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x
          ≤ 1 * (x / (k : ℝ) ^ 2) * (2 * Real.sqrt (Real.log k)) / x := by
            apply div_le_div_of_nonneg_right _ hxpos.le
            have g1 : lrG k * lrCount (x / (k : ℝ) ^ 2)
                ≤ 1 * (x / (k : ℝ) ^ 2) := by
              calc lrG k * lrCount (x / (k : ℝ) ^ 2)
                  ≤ 1 * lrCount (x / (k : ℝ) ^ 2) :=
                    mul_le_mul_of_nonneg_right (lrG_le_one k) (lrCount_nonneg _)
                _ ≤ 1 * (x / (k : ℝ) ^ 2) :=
                    mul_le_mul_of_nonneg_left hHle (by norm_num)
            exact mul_le_mul g1 hsq_le (Real.sqrt_nonneg _)
              (by simpa using hy_nn)
        _ = (2 * Real.sqrt (Real.log k)) / (k : ℝ) ^ 2 := by
              field_simp
        _ ≤ lrBnd D k := by
              unfold lrBnd
              apply div_le_div_of_nonneg_right _ hc0.le
              linarith [hb_main]

/-- `B(x) · √(log x) / x` as a topological sum over `k`. -/
private lemma lr_B_tsum (x : ℝ) :
    lrB x * Real.sqrt (Real.log x) / x
      = ∑' k : ℕ, lrG k * lrCount (x / (k : ℝ) ^ 2)
        * Real.sqrt (Real.log x) / x := by
  have hvan : ∀ k : ℕ, k ∉ Finset.Ioc 0 ⌊x⌋₊ →
      lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x = 0 := by
    intro k hk
    rw [Finset.mem_Ioc, not_and] at hk
    by_cases hk0 : k = 0
    · subst hk0
      simp [lrG_zero]
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hk1pos : 0 < k := hk1
      have hkN : ⌊x⌋₊ < k := lt_of_not_ge (hk hk1pos)
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1pos
      have hc0 : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos hkpos 2
      have hkk : (⌊x⌋₊ : ℝ) + 1 ≤ (k : ℝ) := by
        have h : ⌊x⌋₊ + 1 ≤ k := by omega
        calc (⌊x⌋₊ : ℝ) + 1 = ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by
              rw [Nat.cast_add, Nat.cast_one]
          _ ≤ (k : ℝ) := by exact_mod_cast h
      have hkx : x < (k : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one x) hkk
      have hkk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
        have h1k : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        nlinarith [mul_nonneg hkpos.le (sub_nonneg.mpr h1k)]
      have hlt : x / (k : ℝ) ^ 2 < 1 := by
        rw [div_lt_one hc0]
        exact lt_of_lt_of_le hkx hkk2
      have h0 : lrCount (x / (k : ℝ) ^ 2) = 0 := lrCount_eq_zero_of_lt_one hlt
      simp [h0]
  have e : (∑' k : ℕ, lrG k * lrCount (x / (k : ℝ) ^ 2)
      * Real.sqrt (Real.log x) / x)
      = ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, lrG k * lrCount (x / (k : ℝ) ^ 2)
        * Real.sqrt (Real.log x) / x :=
    tsum_eq_sum hvan
  rw [e]
  unfold lrB
  rw [Finset.sum_mul, Finset.sum_div]

/-- Summability of `lrG k / k ^ 2`. -/
private lemma lr_G_div_sq_summable :
    Summable (fun k : ℕ => lrG k / (k : ℝ) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
  · apply div_nonneg (lrG_nonneg k)
    positivity
  · apply div_le_div_of_nonneg_right (lrG_le_one k) (by positivity)

/-- The `G`-series has positive sum. -/
private lemma lr_G_div_sq_tsum_pos :
    0 < ∑' k : ℕ, lrG k / (k : ℝ) ^ 2 := by
  refine Summable.tsum_pos lr_G_div_sq_summable (fun k => ?_) 1 ?_
  · apply div_nonneg (lrG_nonneg k)
    positivity
  · rw [lrG_one]
    norm_num

/-- Dominated convergence for the `k`-sum: `B(x) · √(log x) / x → c₀ > 0`. -/
private lemma lr_B_tendsto (α : ℝ) (hα : 0 < α)
    (hH : Filter.Tendsto (fun x => lrCount x * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (α / 2))) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      Filter.Tendsto (fun x => lrB x * Real.sqrt (Real.log x) / x)
        Filter.atTop (nhds c₀) := by
  obtain ⟨D, hDpos, hDb⟩ := lr_count_uniform_bound α hα hH
  have hBsum := lr_bnd_summable D
  have hpt : ∀ k : ℕ, Filter.Tendsto
      (fun x => lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (lrG k * (α / 2) / (k : ℝ) ^ 2)) := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk0
    · simp only [lrG_zero, zero_mul, zero_div]
      exact tendsto_const_nhds
    · exact lr_f_tendsto k (Nat.one_le_iff_ne_zero.mpr hk0) α hH
  have hdom : ∀ᶠ x : ℝ in Filter.atTop, ∀ k : ℕ,
      ‖lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x‖
        ≤ lrBnd D k :=
    lr_B_dominated D hDb
  have hlim := tendsto_tsum_of_dominated_convergence hBsum hpt hdom
  have heq : (fun x : ℝ => ∑' k : ℕ, lrG k * lrCount (x / (k : ℝ) ^ 2)
        * Real.sqrt (Real.log x) / x)
      =ᶠ[Filter.atTop] (fun x => lrB x * Real.sqrt (Real.log x) / x) := by
    filter_upwards [Filter.eventually_ge_atTop 0] with x _
    exact (lr_B_tsum x).symm
  have hlimB : Filter.Tendsto (fun x => lrB x * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (∑' k : ℕ, lrG k * (α / 2) / (k : ℝ) ^ 2)) :=
    hlim.congr' heq
  have hS := lr_G_div_sq_tsum_pos
  have htsum_eq : (∑' k : ℕ, lrG k * (α / 2) / (k : ℝ) ^ 2)
      = (α / 2) * (∑' k : ℕ, lrG k / (k : ℝ) ^ 2) := by
    have e : ∀ k : ℕ, lrG k * (α / 2) / (k : ℝ) ^ 2
        = (α / 2) * (lrG k / (k : ℝ) ^ 2) := fun k => by ring
    simp_rw [e]
    exact tsum_mul_left
  refine ⟨(α / 2) * (∑' k : ℕ, lrG k / (k : ℝ) ^ 2),
    mul_pos (by linarith) hS, ?_⟩
  rw [← htsum_eq]
  exact hlimB

/-- `√(log x) / x` tends to `0`. -/
private lemma lr_sqrt_log_div_tendsto :
    Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds 0) := by
  have hbound : ∀ᶠ x : ℝ in Filter.atTop,
      ‖Real.sqrt (Real.log x) / x‖ ≤ x ^ ((-1 / 2 : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hle : Real.sqrt (Real.log x) ≤ Real.sqrt x :=
      Real.sqrt_le_sqrt (Real.log_le_self hxpos.le)
    have e : Real.sqrt x / x = x ^ ((-1 / 2 : ℝ)) := by
      have esub : ((1 / 2 : ℝ) - 1) = -1 / 2 := by norm_num
      rw [Real.sqrt_eq_rpow, ← esub, Real.rpow_sub hxpos, Real.rpow_one]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hxpos.le)]
    calc Real.sqrt (Real.log x) / x ≤ Real.sqrt x / x :=
          div_le_div_of_nonneg_right hle hxpos.le
      _ = x ^ ((-1 / 2 : ℝ)) := e
  have hg : Filter.Tendsto (fun x : ℝ => x ^ ((-1 / 2 : ℝ)))
      Filter.atTop (nhds 0) := by
    have h := tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
    have e : ((-1 / 2 : ℝ)) = -((1 / 2 : ℝ)) := by norm_num
    rw [e]
    simpa using h
  exact squeeze_zero_norm' hbound hg

@[expose] public section

/-- **Landau–Ramanujan theorem.** For real $x$, let $B(x)$ be the number of natural numbers
$m \le x$, including $m = 0$, that can be written as $m = a^2 + b^2$ with natural numbers $a$
and $b$. Then there is a constant $c_0 > 0$ such that $B(x)$ is asymptotically equivalent to
$c_0 x / \sqrt{\log x}$ as $x \to \infty$.

This only asserts the existence of some positive constant $c_0$; it does not identify $c_0$
with the Landau–Ramanujan constant (the Euler product over the primes $p \equiv 3 \pmod 4$ in
the cited result). That identification is an intentional omission relative to the source.

Source: Labib Haddad and Charles Helou,
"Representation of Integers by Near Quadratic Sequences,"
Journal of Integer Sequences 15 (2012),
`https://cs.uwaterloo.ca/journals/JIS/VOL15/Helou/helou3.tex`,
lines 483–486. Complete-source SHA-256
`5441e9d5677d97ca6a836146d5725a10a21bb1e60efa374e366cd803626cd1b1`;
exact cited span (CRLF-preserving) SHA-256
`ce727da79eee9763f20dcbafc1b04c02d719c74c58648eddb71f0e34524e91bf`.
Proof-method source (distinct from the statement source above): the proof
adapts Wirsing's mean-value method as presented in Gérald Tenenbaum,
*Introduction to Analytic and Probabilistic Number Theory*, Chapter III.4.
Concept ID: jis_dep_8a097e6d8b6de10033dfb175;
grounded candidate: jis_grounded_b8d7333e5ca6cb47b348367c;
corrected mentions/papers/proof-uses: 2/1/1.

Proves `Wanted` entry `landau_ramanujan_asymptotic`. -/
public theorem landau_ramanujan_asymptotic :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      Asymptotics.IsEquivalent (Filter.atTop : Filter ℝ)
        (fun x : ℝ =>
          ((Set.ncard {m : ℕ | (m : ℝ) ≤ x ∧ ∃ a b : ℕ, m = a ^ 2 + b ^ 2} : ℕ) : ℝ))
        (fun x : ℝ => c₀ * x / Real.sqrt (Real.log x)) := by
  let f : ℕ →*₀ ℝ :=
    { toFun := lrH, map_one' := lrH_one, map_mul' := lrH_mul,
      map_zero' := lrH_zero }
  have hprime (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
      f p = if (p : ZMod 4) = 1 then 1 else 0 := by
    change lrH p = _
    rw [lrH_prime_eq hp, ← ZMod.natCast_mod p 4]
    have hodd := Nat.odd_iff.mp (hp.eq_two_or_odd'.resolve_left h2)
    have h : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases h with h | h <;> rw [h] <;> rfl
  obtain ⟨α, hαpos, _, hH⟩ :=
    exists_tendsto_sum_of_prime_mod_four f lrH_nonneg lrH_le_one 1 isUnit_one hprime
  obtain ⟨c₀, hc₀pos, hB⟩ := lr_B_tendsto α hαpos hH
  have hcount : ∀ᶠ x : ℝ in Filter.atTop,
      ((Set.ncard {m : ℕ | (m : ℝ) ≤ x ∧ ∃ a b : ℕ, m = a ^ 2 + b ^ 2} : ℕ) : ℝ)
        = lrB x + 1 := by
    filter_upwards [Filter.eventually_ge_atTop 0] with x hx
    have h1 := lr_ncard_eq hx
    have h2 := lr_twoSq_count_eq hx
    rw [h1, Nat.cast_add, Nat.cast_one, h2]
  have hratio : Filter.Tendsto
      (fun x : ℝ => ((Set.ncard {m : ℕ | (m : ℝ) ≤ x ∧
        ∃ a b : ℕ, m = a ^ 2 + b ^ 2} : ℕ) : ℝ)
        / (c₀ * x / Real.sqrt (Real.log x)))
      Filter.atTop (nhds 1) := by
    have heq : (fun x : ℝ => ((Set.ncard {m : ℕ | (m : ℝ) ≤ x ∧
          ∃ a b : ℕ, m = a ^ 2 + b ^ 2} : ℕ) : ℝ)
          / (c₀ * x / Real.sqrt (Real.log x)))
        =ᶠ[Filter.atTop]
        (fun x : ℝ => (lrB x * Real.sqrt (Real.log x) / x
          + Real.sqrt (Real.log x) / x) / c₀) := by
      filter_upwards [Filter.eventually_gt_atTop 1, hcount] with x hx1 hcx
      have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx1
      have hsq : Real.sqrt (Real.log x) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr hlog)
      have hxx : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx1)
      have hc : c₀ ≠ 0 := ne_of_gt hc₀pos
      rw [hcx]
      field_simp
    have hB' : Filter.Tendsto
        (fun x : ℝ => lrB x * Real.sqrt (Real.log x) / x
          + Real.sqrt (Real.log x) / x)
        Filter.atTop (nhds (c₀ + 0)) :=
      hB.add lr_sqrt_log_div_tendsto
    rw [add_zero] at hB'
    have hdiv : Filter.Tendsto
        (fun x : ℝ => (lrB x * Real.sqrt (Real.log x) / x
          + Real.sqrt (Real.log x) / x) / c₀)
        Filter.atTop (nhds (c₀ / c₀)) :=
      hB'.div_const c₀
    have hc0 : c₀ ≠ 0 := ne_of_gt hc₀pos
    rw [div_self hc0] at hdiv
    exact hdiv.congr' heq.symm
  refine ⟨c₀, hc₀pos, ?_⟩
  exact Asymptotics.isEquivalent_of_tendsto_one hratio

end

end MetaMathlibExt
