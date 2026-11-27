/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ValuationSubring_mem_iff_mem_of_mem_adjoin_simple_of_forall_aeval_inv_mem.lean`
and
`P2M/Sol/S_ValuationSubring_mem_iff_mem_of_mem_adjoin_simple_of_forall_aeval_inv_mem.lean`
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

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

import Mathlib.Algebra.Polynomial.Lifts

@[expose] public section

open scoped Polynomial

namespace ValuationSubring

private theorem exists_eq_C_mul_of_ne_zero {L : Type*} [Field L] (A : ValuationSubring L)
    (p : L[X]) (hp : p ≠ 0) :
    ∃ (c : L) (p₁ : L[X]) (n₀ : ℕ), c ≠ 0 ∧ p = Polynomial.C c * p₁ ∧
      (∀ n, p₁.coeff n ∈ A) ∧ p₁.coeff n₀ = 1 := by
  have hne : p.support.Nonempty := Polynomial.support_nonempty.mpr hp
  obtain ⟨n₀, hn₀, hmax⟩ := Finset.exists_max_image p.support (fun n => A.valuation (p.coeff n)) hne
  have hc : p.coeff n₀ ≠ 0 := Polynomial.mem_support_iff.mp hn₀
  refine ⟨p.coeff n₀, Polynomial.C (p.coeff n₀)⁻¹ * p, n₀, hc, ?_, ?_, ?_⟩
  · rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1, one_mul]
  · intro n
    rw [Polynomial.coeff_C_mul]
    by_cases hn : n ∈ p.support
    · rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
      have h1 := hmax n hn
      have hc' : A.valuation (p.coeff n₀) ≠ 0 := by rwa [ne_eq, map_eq_zero]
      calc (A.valuation (p.coeff n₀))⁻¹ * A.valuation (p.coeff n)
          ≤ (A.valuation (p.coeff n₀))⁻¹ * A.valuation (p.coeff n₀) := mul_le_mul_right h1 _
        _ = 1 := inv_mul_cancel₀ hc'
    · rw [Polynomial.notMem_support_iff.mp hn, mul_zero]
      exact zero_mem A
  · rw [Polynomial.coeff_C_mul, inv_mul_cancel₀ hc]

private theorem mem_iff_mem_of_mem_adjoin {L F : Type*} [Field L] [Field F] [Algebra L F]
    (A : ValuationSubring L) (S₁ S₂ : Subring F)
    (h₁A : ∀ a : L, algebraMap L F a ∈ S₁ ↔ a ∈ A)
    (h₂A : ∀ a : L, algebraMap L F a ∈ S₂ ↔ a ∈ A) (x : F)
    (hu₁ : ∀ p : L[X], (∀ n, p.coeff n ∈ A) → (∃ n₀, p.coeff n₀ = 1) →
      Polynomial.aeval x p ∈ S₁ ∧ (Polynomial.aeval x p)⁻¹ ∈ S₁)
    (hu₂ : ∀ p : L[X], (∀ n, p.coeff n ∈ A) → (∃ n₀, p.coeff n₀ = 1) →
      Polynomial.aeval x p ∈ S₂ ∧ (Polynomial.aeval x p)⁻¹ ∈ S₂)
    (e : F) (he : e ∈ IntermediateField.adjoin L ({x} : Set F)) :
    e ∈ S₁ ↔ e ∈ S₂ := by
  rw [IntermediateField.mem_adjoin_simple_iff] at he
  obtain ⟨r, s, rfl⟩ := he
  have key : ∀ (S : Subring F) (u y : F), u ≠ 0 → u ∈ S → u⁻¹ ∈ S →
      (y * u ∈ S ↔ y ∈ S) := by
    intro S u y hu0 hu hui
    constructor
    · intro h
      have hEq : y = y * u * u⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hu0, mul_one]
      rw [hEq]
      exact Subring.mul_mem _ h hui
    · intro h
      exact Subring.mul_mem _ h hu
  by_cases hs : Polynomial.aeval x s = 0
  · rw [hs, div_zero]; exact ⟨fun _ => S₂.zero_mem, fun _ => S₁.zero_mem⟩
  by_cases hr : Polynomial.aeval x r = 0
  · rw [hr, zero_div]; exact ⟨fun _ => S₂.zero_mem, fun _ => S₁.zero_mem⟩
  have hs' : s ≠ 0 := by rintro rfl; exact hs (map_zero _)
  have hr' : r ≠ 0 := by rintro rfl; exact hr (map_zero _)
  obtain ⟨c, r₁, n₁, hc, hrr, hr₁A, hr₁⟩ := exists_eq_C_mul_of_ne_zero A r hr'
  obtain ⟨d, s₁, m₁, hd, hss, hs₁A, hs₁⟩ := exists_eq_C_mul_of_ne_zero A s hs'
  obtain ⟨hr₁S₁, hr₁S₁i⟩ := hu₁ r₁ hr₁A ⟨n₁, hr₁⟩
  obtain ⟨hs₁S₁, hs₁S₁i⟩ := hu₁ s₁ hs₁A ⟨m₁, hs₁⟩
  obtain ⟨hr₁S₂, hr₁S₂i⟩ := hu₂ r₁ hr₁A ⟨n₁, hr₁⟩
  obtain ⟨hs₁S₂, hs₁S₂i⟩ := hu₂ s₁ hs₁A ⟨m₁, hs₁⟩
  have hs₁0 : Polynomial.aeval x s₁ ≠ 0 := by
    intro h0
    apply hs
    rw [hss, map_mul, h0, mul_zero]
  have hr₁0 : Polynomial.aeval x r₁ ≠ 0 := by
    intro h0
    apply hr
    rw [hrr, map_mul, h0, mul_zero]
  have hexpr : Polynomial.aeval x r / Polynomial.aeval x s =
      algebraMap L F (c / d) * (Polynomial.aeval x r₁ * (Polynomial.aeval x s₁)⁻¹) := by
    rw [hrr, hss, map_mul, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, map_div₀]
    field_simp
  rw [hexpr]
  have hu : ∀ (S : Subring F), Polynomial.aeval x r₁ ∈ S → (Polynomial.aeval x r₁)⁻¹ ∈ S →
      Polynomial.aeval x s₁ ∈ S → (Polynomial.aeval x s₁)⁻¹ ∈ S →
      (algebraMap L F (c / d) * (Polynomial.aeval x r₁ * (Polynomial.aeval x s₁)⁻¹) ∈ S ↔
        algebraMap L F (c / d) ∈ S) := by
    intro S h1 h1i h2 h2i
    refine key S _ _ (mul_ne_zero hr₁0 (inv_ne_zero hs₁0)) (Subring.mul_mem _ h1 h2i) ?_
    rw [mul_inv, inv_inv]
    exact Subring.mul_mem _ h1i h2
  rw [hu S₁ hr₁S₁ hr₁S₁i hs₁S₁ hs₁S₁i, hu S₂ hr₁S₂ hr₁S₂i hs₁S₂ hs₁S₂i, h₁A, h₂A]

private theorem algebraMap_mem_iff {L F : Type*} [Field L] [Field F] [Algebra L F]
    (A₀ : ValuationSubring L) [Algebra ↥A₀ F] [IsScalarTower ↥A₀ L F]
    (ϖ : ↥A₀) (hϖ : IsLocalRing.maximalIdeal ↥A₀ = Ideal.span {ϖ})
    (V : ValuationSubring F)
    (hV : ∀ r : ↥A₀, algebraMap ↥A₀ F r ∈ V) (hϖV : algebraMap ↥A₀ F ϖ ∈ V.nonunits) :
    ∀ a : L, algebraMap L F a ∈ V ↔ a ∈ A₀ := by
  have halg : ∀ r : ↥A₀, algebraMap ↥A₀ F r = algebraMap L F (r : L) := fun r =>
    IsScalarTower.algebraMap_apply ↥A₀ L F r
  intro a
  constructor
  · intro haV
    by_contra haA
    have ha0 : a ≠ 0 := by rintro rfl; exact haA A₀.zero_mem
    have hinvA : a⁻¹ ∈ A₀ := by
      rcases A₀.mem_or_inv_mem a with h | h
      · exact absurd h haA
      · exact h
    have hgt : 1 < A₀.valuation a := by
      rw [← not_le, A₀.valuation_le_one_iff]; exact haA
    have hinv𝔪 : (⟨a⁻¹, hinvA⟩ : ↥A₀) ∈ IsLocalRing.maximalIdeal ↥A₀ :=
      (A₀.valuation_lt_one_iff _).mpr ((Valuation.one_lt_val_iff A₀.valuation ha0).mp hgt)
    rw [hϖ] at hinv𝔪
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hinv𝔪
    have hlt : V.valuation (algebraMap L F a⁻¹) < 1 := by
      have hEq : algebraMap L F a⁻¹ = algebraMap ↥A₀ F b * algebraMap ↥A₀ F ϖ := by
        rw [← map_mul, hb, halg]
      rw [hEq, map_mul]
      calc V.valuation (algebraMap ↥A₀ F b) * V.valuation (algebraMap ↥A₀ F ϖ)
          ≤ 1 * V.valuation (algebraMap ↥A₀ F ϖ) :=
            mul_le_mul_left ((V.valuation_le_one_iff _).mpr (hV b)) _
        _ < 1 := by rw [one_mul]; exact (V.mem_nonunits_iff).mp hϖV
    have hle : V.valuation (algebraMap L F a) ≤ 1 := (V.valuation_le_one_iff _).mpr haV
    have h1 : V.valuation (algebraMap L F a * algebraMap L F a⁻¹) < 1 := by
      rw [map_mul]
      calc V.valuation (algebraMap L F a) * V.valuation (algebraMap L F a⁻¹)
          ≤ 1 * V.valuation (algebraMap L F a⁻¹) := mul_le_mul_left hle _
        _ < 1 := by rw [one_mul]; exact hlt
    rw [← map_mul, mul_inv_cancel₀ ha0, map_one, map_one] at h1
    exact lt_irrefl _ h1
  · intro haA
    rw [← show algebraMap ↥A₀ F ⟨a, haA⟩ = algebraMap L F a from halg ⟨a, haA⟩]
    exact hV ⟨a, haA⟩

private theorem aeval_mem_and_inv_mem {L F : Type*} [Field L] [Field F] [Algebra L F]
    (A₀ : ValuationSubring L) [Algebra ↥A₀ F] [IsScalarTower ↥A₀ L F]
    (ϖ : ↥A₀) (hϖ : IsLocalRing.maximalIdeal ↥A₀ = Ideal.span {ϖ})
    (x : F) (V : ValuationSubring F)
    (hxV : ∀ P : Polynomial ↥A₀, ¬ (Polynomial.C ϖ ∣ P) →
      Polynomial.aeval x P ∈ V ∧ (Polynomial.aeval x P)⁻¹ ∈ V) :
    ∀ p : L[X], (∀ n, p.coeff n ∈ A₀) → (∃ n₀, p.coeff n₀ = 1) →
      Polynomial.aeval x p ∈ V.toSubring ∧ (Polynomial.aeval x p)⁻¹ ∈ V.toSubring := by
  intro p hp hn
  obtain ⟨n₀, hn₀⟩ := hn
  have hlift : p ∈ Polynomial.lifts (algebraMap ↥A₀ L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨p.coeff n, hp n⟩, rfl⟩
  obtain ⟨P, hP⟩ := (Polynomial.mem_lifts _).mp hlift
  have hPx : Polynomial.aeval x P = Polynomial.aeval x p := by
    rw [← hP, Polynomial.aeval_map_algebraMap]
  have hndvd : ¬ (Polynomial.C ϖ ∣ P) := by
    intro hdvd
    have h1 : ϖ ∣ P.coeff n₀ := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hdvd n₀
    have h2 : P.coeff n₀ = 1 := by
      have hinj : Function.Injective (algebraMap ↥A₀ L) := fun a b h => Subtype.ext h
      apply hinj
      rw [map_one, ← Polynomial.coeff_map, hP, hn₀]
    rw [h2] at h1
    have hunit : IsUnit ϖ := isUnit_of_dvd_one h1
    have hmem : ϖ ∈ IsLocalRing.maximalIdeal ↥A₀ := by
      rw [hϖ]; exact Ideal.mem_span_singleton_self _
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem hunit
  obtain ⟨h1, h2⟩ := hxV P hndvd
  rw [hPx] at h1 h2
  exact ⟨h1, h2⟩

/-- Two valuation subrings of `F` that both extend `A₀`, send a uniformizer of
`A₀` to a nonunit, and pass the same integrality test on every polynomial in
`x` whose coefficients are not all divisible by the uniformizer, agree on the
simple extension `L(x)`. -/
public theorem mem_iff_mem_of_mem_adjoin_simple_of_forall_aeval_inv_mem
    (L : Type*) [Field L] (A₀ : ValuationSubring L)
    (ϖ : ↥A₀) (hϖ : IsLocalRing.maximalIdeal ↥A₀ = Ideal.span {ϖ})
    (F : Type*) [Field F] [Algebra L F] [Algebra ↥A₀ F] [IsScalarTower ↥A₀ L F]
    (x : F) (V V' : ValuationSubring F)
    (hV : ∀ r : ↥A₀, algebraMap ↥A₀ F r ∈ V) (hϖV : algebraMap ↥A₀ F ϖ ∈ V.nonunits)
    (hxV : ∀ P : Polynomial ↥A₀, ¬ (Polynomial.C ϖ ∣ P) →
      Polynomial.aeval x P ∈ V ∧ (Polynomial.aeval x P)⁻¹ ∈ V)
    (hV' : ∀ r : ↥A₀, algebraMap ↥A₀ F r ∈ V') (hϖV' : algebraMap ↥A₀ F ϖ ∈ V'.nonunits)
    (hxV' : ∀ P : Polynomial ↥A₀, ¬ (Polynomial.C ϖ ∣ P) →
      Polynomial.aeval x P ∈ V' ∧ (Polynomial.aeval x P)⁻¹ ∈ V') :
    ∀ e : F, e ∈ IntermediateField.adjoin L ({x} : Set F) → (e ∈ V ↔ e ∈ V') := by
  intro e he
  exact mem_iff_mem_of_mem_adjoin A₀ V.toSubring V'.toSubring
    (algebraMap_mem_iff A₀ ϖ hϖ V hV hϖV) (algebraMap_mem_iff A₀ ϖ hϖ V' hV' hϖV') x
    (aeval_mem_and_inv_mem A₀ ϖ hϖ x V hxV) (aeval_mem_and_inv_mem A₀ ϖ hϖ x V' hxV') e he

end ValuationSubring
