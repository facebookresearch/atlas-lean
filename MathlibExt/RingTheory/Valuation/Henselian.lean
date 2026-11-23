/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed.lean` and
`P2M/Sol/S_ValuationSubring_henselianLocalRing_of_isAlgClosed.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Henselian valuation subrings

A valuation subring of an algebraically closed field is Henselian: roots
of monic polynomials over the subring lie in it, so Hensel's lemma follows
by factoring off one root at a time.
-/

@[expose] public section

open IsLocalRing Polynomial

namespace HenselianValuationAux

variable {L : Type*} [Field L] (A : ValuationSubring L)

private theorem mem_of_isRoot_map {f : A[X]} (hf : f.Monic) {r : L}
    (hr : (f.map A.subtype).IsRoot r) : r ∈ A := by
  by_contra hrA
  have hr0 : r ≠ 0 := by rintro rfl; exact hrA A.zero_mem
  have hinv : r⁻¹ ∈ A := (A.mem_or_inv_mem r).resolve_left hrA
  have hinv𝔪 : (⟨r⁻¹, hinv⟩ : A) ∈ maximalIdeal A := by
    rw [mem_maximalIdeal]
    change ¬ IsUnit (⟨r⁻¹, hinv⟩ : A)
    intro hu
    obtain ⟨w, hw⟩ := hu.exists_left_inv
    have hw' : (w : L) * r⁻¹ = 1 := by
      have hthis := congrArg (fun x : A => (x : L)) hw
      simpa using hthis
    rw [mul_inv_eq_one₀ hr0] at hw'
    exact hrA (hw' ▸ w.2)
  set n := f.natDegree with hn
  have hroot : (f.map A.subtype).eval r = 0 := hr
  rw [eval_map, eval₂_eq_sum_range, Finset.sum_range_succ, Monic.coeff_natDegree hf] at hroot
  simp only [map_one, one_mul] at hroot
  have key : (1 : L) = - ∑ i ∈ Finset.range n, A.subtype (f.coeff i) * (r⁻¹) ^ (n - i) := by
    have h1 : r ^ n * (r⁻¹) ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ hr0, one_pow]
    have h2 : ∀ i ∈ Finset.range n, A.subtype (f.coeff i) * r ^ i * (r⁻¹) ^ n =
        A.subtype (f.coeff i) * (r⁻¹) ^ (n - i) := by
      intro i hi
      have hi' : i ≤ n := (Finset.mem_range.mp hi).le
      rw [mul_assoc]
      congr 1
      have e : (r⁻¹) ^ n = (r⁻¹) ^ i * (r⁻¹) ^ (n - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hi']
      rw [e, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hr0, one_pow, one_mul]
    have h3 := congrArg (fun x => x * (r⁻¹) ^ n) hroot
    simp only [add_mul, zero_mul, Finset.sum_mul] at h3
    rw [h1, Finset.sum_congr rfl h2] at h3
    linear_combination h3
  set y : A := - ∑ i ∈ Finset.range n, f.coeff i * (⟨r⁻¹, hinv⟩ : A) ^ (n - i) with hy
  have hy𝔪 : y ∈ maximalIdeal A := by
    refine (Ideal.neg_mem_iff _).mpr (Ideal.sum_mem _ fun i hi => ?_)
    have hni : 0 < n - i := Nat.sub_pos_of_lt (Finset.mem_range.mp hi)
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hinv𝔪 _ hni)
  have hy1 : y = 1 := by
    apply Subtype.ext
    rw [hy]
    simp only [OneMemClass.coe_one]
    rw [key]
    simp
  rw [hy1] at hy𝔪
  exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr hy𝔪)

variable [IsAlgClosed L]

private theorem exists_isRoot_and_sub_mem :
    ∀ (n : ℕ) (f : A[X]), f.Monic → f.natDegree = n →
      ∀ a₀ : A, f.eval a₀ ∈ maximalIdeal A →
        ∃ a : A, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal A := by
  intro n
  induction n with
  | zero =>
    intro f hf hdeg a₀ ha₀
    have hf1 : f = 1 := (Monic.natDegree_eq_zero hf).mp hdeg
    rw [hf1, eval_one] at ha₀
    exact absurd ((Ideal.eq_top_iff_one _).mpr ha₀) (maximalIdeal.isMaximal A).ne_top
  | succ n ih =>
    intro f hf hdeg a₀ ha₀
    have hdeg' : (f.map A.subtype).degree ≠ 0 := by
      rw [degree_map_eq_of_injective Subtype.val_injective,
        degree_eq_natDegree (Monic.ne_zero hf), hdeg]
      exact_mod_cast Nat.succ_ne_zero n
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (f.map A.subtype) hdeg'
    have hrA : r ∈ A := mem_of_isRoot_map A hf hr
    have hroot : f.IsRoot ⟨r, hrA⟩ := by
      have h1 : A.subtype (f.eval ⟨r, hrA⟩) = 0 := by
        rw [← eval₂_hom, ← eval_map]; exact hr
      exact (map_eq_zero_iff _ Subtype.val_injective).mp h1
    set f₁ := f /ₘ (X - C (⟨r, hrA⟩ : A)) with hf₁
    have hfac : (X - C (⟨r, hrA⟩ : A)) * f₁ = f := mul_divByMonic_eq_iff_isRoot.mpr hroot
    by_cases hcase : (⟨r, hrA⟩ : A) - a₀ ∈ maximalIdeal A
    · exact ⟨_, hroot, hcase⟩
    · have hf₁mon : f₁.Monic :=
        Monic.of_mul_monic_left (monic_X_sub_C _) (by rw [hfac]; exact hf)
      have hf₁deg : f₁.natDegree = n := by
        have h := congrArg natDegree hfac
        rw [Monic.natDegree_mul (monic_X_sub_C _) hf₁mon, natDegree_X_sub_C, hdeg] at h
        omega
      have hf₁a₀ : f₁.eval a₀ ∈ maximalIdeal A := by
        have h := congrArg (eval a₀) hfac
        rw [eval_mul, eval_sub, eval_X, eval_C] at h
        rw [← h] at ha₀
        rcases (maximalIdeal.isMaximal A).isPrime.mem_or_mem ha₀ with h1 | h1
        · refine absurd ?_ hcase
          have h2 := (Ideal.neg_mem_iff _).mpr h1
          rwa [neg_sub] at h2
        · exact h1
      obtain ⟨a, ha, haa₀⟩ := ih f₁ hf₁mon hf₁deg a₀ hf₁a₀
      refine ⟨a, ?_, haa₀⟩
      change f.eval a = 0
      rw [← hfac, eval_mul, ha.eq_zero, mul_zero]

private theorem henselianLocalRing : HenselianLocalRing A where
  toIsLocalRing := inferInstance
  is_henselian f hf a₀ h₀ _ := exists_isRoot_and_sub_mem A f.natDegree f hf rfl a₀ h₀

end HenselianValuationAux

/-- A valuation subring of an algebraically closed field is Henselian. -/
theorem ValuationSubring.henselianLocalRing_of_isAlgClosed {L : Type*} [Field L]
    [IsAlgClosed L] (A : ValuationSubring L) : HenselianLocalRing A :=
  HenselianValuationAux.henselianLocalRing A
