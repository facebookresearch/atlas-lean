/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime.lean`
and
`P2M/Sol/S_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime.lean`
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

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import MathlibExt.RingTheory.Valuation.LiesOverPrime

import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Integral representation at a place above a prime

An element of a valuation subring of `AlgebraicClosure ℚ` lying over a
rational prime can be written, after multiplication by an integral element
that is a unit at the place, as an integral element.
-/

@[expose] public section

open scoped NumberField

namespace ValuationSubring

/-- An element of a valuation subring of `AlgebraicClosure ℚ` lying over
a rational prime `q` can be scaled by an integral element that is a unit
at the place to an integral element. -/
public theorem exists_integral_mul_eq_of_liesOverPrime
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) (a : AlgebraicClosure ℚ) (ha : a ∈ A) :
    ∃ x s : integralClosure ℤ (AlgebraicClosure ℚ),
      (s : AlgebraicClosure ℚ) ∉ A.nonunits ∧ a * s = x := by
  classical

  haveI halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _
        (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h

  have int_mem : ∀ b : (AlgebraicClosure ℚ), IsIntegral ℤ b → b ∈ A := by
    intro b hb

    have hbA : IsIntegral A b := by
      obtain ⟨p, hp, hpb⟩ := hb
      refine ⟨p.map (Int.castRingHom A), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have : (algebraMap A (AlgebraicClosure ℚ)).comp (Int.castRingHom A)
          = algebraMap ℤ (AlgebraicClosure ℚ) := RingHom.ext_int _ _
      rw [this]
      exact hpb
    obtain ⟨y, hy⟩ :=
      (IsIntegrallyClosed.isIntegral_iff (R := A) (K := AlgebraicClosure ℚ)).mp hbA
    rw [← hy]
    exact y.2

  by_cases ha0 : a = 0
  · refine ⟨0, 1, ?_, by simp [ha0]⟩
    rw [OneMemClass.coe_one, ValuationSubring.mem_nonunits_iff, map_one]
    exact lt_irrefl 1

  have haint : IsIntegral ℚ a := Algebra.IsIntegral.isIntegral a
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {a}
  haveI hFfd : FiniteDimensional ℚ F := IntermediateField.adjoin.finiteDimensional haint
  haveI : NumberField F :=
    { to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
      to_finiteDimensional := hFfd }

  have exists_div_rep_or_inv_div_rep_of_ne_bot :
      ∀ (P : Ideal (𝓞 F)) [P.IsPrime] (hP : P ≠ ⊥) (x : F) (hx : x ≠ 0),
      (∃ a s : 𝓞 F, s ∉ P ∧ x = algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F s) ∨
        ∃ a s : 𝓞 F, a ∈ P ∧ s ∉ P ∧ x⁻¹ = algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F s
    := by
    intro P _ hP x hx
    obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
    have hφ : Function.Injective (algebraMap (𝓞 F) F) := IsFractionRing.injective (𝓞 F) F
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_div] at hnd
      exact hx hnd.symm
    have hnF : algebraMap (𝓞 F) F n ≠ 0 := fun h0 => hn0 (hφ (by rw [h0, map_zero]))
    have hdF : algebraMap (𝓞 F) F d ≠ 0 := fun h0 => hd0 (hφ (by rw [h0, map_zero]))
    haveI : IsDomain (Localization.AtPrime P) :=
      IsLocalization.isDomain_of_local_atPrime ‹P.IsPrime›
    haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 F) hP _
    obtain ⟨c, hc | hc⟩ :=
      ValuationRing.cond (algebraMap (𝓞 F) (Localization.AtPrime P) n)
        (algebraMap (𝓞 F) (Localization.AtPrime P) d)
    ·
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
      have hsP : (s : 𝓞 F) ∉ P := s.2
      have hsF : algebraMap (𝓞 F) F (s : 𝓞 F) ≠ 0 := fun h0 =>
        hsP (by rw [show (s : 𝓞 F) = 0 from hφ (by rw [h0, map_zero])]; exact P.zero_mem)
      have key : algebraMap (𝓞 F) (Localization.AtPrime P) (n * a)
          = algebraMap (𝓞 F) (Localization.AtPrime P) (d * s) := by
        rw [map_mul, map_mul, ← IsLocalization.mk'_spec (Localization.AtPrime P) a s, ← hc]
        ring
      obtain ⟨t, ht⟩ :=
        (IsLocalization.eq_iff_exists P.primeCompl (Localization.AtPrime P)).mp key
      have ht0 : (t : 𝓞 F) ≠ 0 :=
        nonZeroDivisors.ne_zero (P.primeCompl_le_nonZeroDivisors t.2)
      have hEq : n * a = d * (s : 𝓞 F) := mul_left_cancel₀ ht0 ht
      have hF : algebraMap (𝓞 F) F n * algebraMap (𝓞 F) F a
          = algebraMap (𝓞 F) F d * algebraMap (𝓞 F) F (s : 𝓞 F) := by
        rw [← map_mul, ← map_mul, hEq]
      have hxinv : x⁻¹ = algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F (s : 𝓞 F) := by
        rw [← hnd, inv_div, div_eq_div_iff hnF hsF]
        linear_combination -hF
      by_cases haP : a ∈ P
      · exact Or.inr ⟨a, s, haP, hsP, hxinv⟩
      · refine Or.inl ⟨(s : 𝓞 F), a, haP, ?_⟩
        rw [← inv_inv x, hxinv, inv_div]
    ·
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
      have hsP : (s : 𝓞 F) ∉ P := s.2
      have hsF : algebraMap (𝓞 F) F (s : 𝓞 F) ≠ 0 := fun h0 =>
        hsP (by rw [show (s : 𝓞 F) = 0 from hφ (by rw [h0, map_zero])]; exact P.zero_mem)
      have key : algebraMap (𝓞 F) (Localization.AtPrime P) (d * a)
          = algebraMap (𝓞 F) (Localization.AtPrime P) (n * s) := by
        rw [map_mul, map_mul, ← IsLocalization.mk'_spec (Localization.AtPrime P) a s, ← hc]
        ring
      obtain ⟨t, ht⟩ :=
        (IsLocalization.eq_iff_exists P.primeCompl (Localization.AtPrime P)).mp key
      have ht0 : (t : 𝓞 F) ≠ 0 :=
        nonZeroDivisors.ne_zero (P.primeCompl_le_nonZeroDivisors t.2)
      have hEq : d * a = n * (s : 𝓞 F) := mul_left_cancel₀ ht0 ht
      have hF : algebraMap (𝓞 F) F d * algebraMap (𝓞 F) F a
          = algebraMap (𝓞 F) F n * algebraMap (𝓞 F) F (s : 𝓞 F) := by
        rw [← map_mul, ← map_mul, hEq]
      refine Or.inl ⟨a, s, hsP, ?_⟩
      rw [← hnd, div_eq_div_iff hdF hsF]
      linear_combination -hF


  have hOA : ∀ b : 𝓞 F,
      algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F b) ∈ A := fun b =>
    int_mem _ (map_isIntegral_int (algebraMap F (AlgebraicClosure ℚ))
      (NumberField.RingOfIntegers.isIntegral_coe b))
  let φ : 𝓞 F →+* A :=
    ((algebraMap F (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 F) F)).codRestrict
      A.toSubring (fun b => hOA b)
  have hφ : ∀ b : 𝓞 F, (φ b : (AlgebraicClosure ℚ)) =
      algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F b) := fun b => rfl
  let P : Ideal (𝓞 F) := Ideal.comap φ (IsLocalRing.maximalIdeal A)
  haveI hPprime : P.IsPrime := Ideal.IsPrime.comap φ
  have hmemP : ∀ b : 𝓞 F, b ∈ P ↔
      algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F b) ∈ A.nonunits := by
    intro b
    rw [← hφ, ValuationSubring.coe_mem_nonunits_iff]
    rfl

  have hqP : (q : 𝓞 F) ∈ P := by
    rw [hmemP, map_natCast, map_natCast]
    exact hA
  have hPbot : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.mem_bot] at hqP
    exact hq.ne_zero (Nat.cast_eq_zero.mp hqP)

  have hval1 : ∀ s : 𝓞 F, s ∉ P →
      A.valuation (algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F s)) = 1 := by
    intro s hs
    refine le_antisymm ((A.valuation_le_one_iff _).mpr (hOA s)) (not_lt.mp fun hlt => hs ?_)
    rw [hmemP, ValuationSubring.mem_nonunits_iff]
    exact hlt

  let a' : F := ⟨a, IntermediateField.mem_adjoin_simple_self ℚ a⟩
  have ha' : algebraMap F (AlgebraicClosure ℚ) a' = a := rfl
  have ha'0 : a' ≠ 0 := fun h => ha0 (by rw [← ha', h, map_zero])

  have hint : ∀ b : 𝓞 F,
      IsIntegral ℤ (algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F b)) := fun b =>
    map_isIntegral_int (algebraMap F (AlgebraicClosure ℚ))
      (NumberField.RingOfIntegers.isIntegral_coe b)
  rcases exists_div_rep_or_inv_div_rep_of_ne_bot P hPbot a' ha'0 with
    ⟨b, s, hs, hrep⟩ | ⟨b, s, hb, hs, hrep⟩
  ·
    have hsK : algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F s) ≠ 0 := by
      intro h0
      have := hval1 s hs
      rw [h0, map_zero] at this
      exact zero_ne_one this
    refine ⟨⟨_, hint b⟩, ⟨_, hint s⟩, ?_, ?_⟩
    · change algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F s) ∉ A.nonunits
      rw [ValuationSubring.mem_nonunits_iff, hval1 s hs]
      exact lt_irrefl 1
    · change a * algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F s) =
        algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F b)
      rw [← ha', hrep, map_div₀, div_mul_cancel₀ _ hsK]
  ·
    exfalso
    have hlt : A.valuation a⁻¹ < 1 := by
      have : a⁻¹ = algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F b) /
          algebraMap F (AlgebraicClosure ℚ) (algebraMap (𝓞 F) F s) := by
        rw [← ha', ← map_inv₀, hrep, map_div₀]
      rw [this, map_div₀, hval1 s hs, div_one, ← ValuationSubring.mem_nonunits_iff, ← hmemP]
      exact hb
    have hle : A.valuation a ≤ 1 := (A.valuation_le_one_iff a).mpr ha
    have hone : A.valuation a * A.valuation a⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ ha0, map_one]
    have hprod : A.valuation a * A.valuation a⁻¹ < 1 := by
      calc A.valuation a * A.valuation a⁻¹ ≤ A.valuation a⁻¹ := mul_le_of_le_one_left' hle
        _ < 1 := hlt
    exact absurd hone (ne_of_lt hprod)

end ValuationSubring
