/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_QuasiFinite_of_flat_of_finiteType_of_moduleFinite_
baseChange_fractionRing.lean`
and
`P2M/Sol/S_Algebra_QuasiFinite_of_flat_of_finiteType_of_moduleFinite_baseChange_fractionRing.lean`
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

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.QuasiFinite.Basic

import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Polynomial.Content

@[expose] public section

set_option maxHeartbeats 800000

open scoped TensorProduct nonZeroDivisors
open Polynomial

universe u v w

section Helpers

variable {R : Type u} [CommRing R] [IsDomain R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {S : Type w} [CommRing S] [Algebra R S]

private theorem includeRight_injective [Module.Flat R S] :
    Function.Injective (Algebra.TensorProduct.includeRight : S →ₐ[R] K ⊗[R] S) := by
  have h1 : Function.Injective ((Algebra.linearMap R K).rTensor S) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective R K)
  intro a b hab
  have h : (Algebra.linearMap R K).rTensor S ((TensorProduct.lid R S).symm a) =
      (Algebra.linearMap R K).rTensor S ((TensorProduct.lid R S).symm b) := by
    simpa [LinearMap.rTensor_tmul] using hab
  exact (TensorProduct.lid R S).symm.injective (h1 h)

private theorem exists_ne_zero_aeval_eq_zero [Module.Flat R S]
    [Module.Finite K (K ⊗[R] S)] (s : S) :
    ∃ f : R[X], f ≠ 0 ∧ aeval s f = 0 := by
  have hint : IsIntegral K ((1 : K) ⊗ₜ[R] s : K ⊗[R] S) := Algebra.IsIntegral.isIntegral _
  obtain ⟨g, hgmon, hg⟩ := hint
  refine ⟨IsLocalization.integerNormalization R⁰ g, ?_, ?_⟩
  · intro h0
    obtain ⟨b, hb, hbg⟩ := IsLocalization.integerNormalization_spec R⁰ g
    rw [h0, Polynomial.map_zero] at hbg
    have hb0 : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hc := congrArg (fun p : K[X] => p.coeff g.natDegree) hbg
    simp only [Polynomial.coeff_zero, Polynomial.coeff_smul, hgmon.coeff_natDegree] at hc
    apply hb0
    rw [Algebra.algebraMap_eq_smul_one]
    exact hc.symm
  · apply includeRight_injective (R := R) (K := K)
    rw [map_zero, ← Polynomial.aeval_algHom_apply, Algebra.TensorProduct.includeRight_apply]
    exact IsLocalization.integerNormalization_aeval_eq_zero R⁰ g hg

private theorem exists_aeval_eq_zero_not_forall_coeff_mem [IsPrincipalIdealRing R]
    [Module.Flat R S] [Module.Finite K (K ⊗[R] S)] (P : Ideal R) (hP : P ≠ ⊤) (s : S) :
    ∃ f : R[X], aeval s f = 0 ∧ ∃ i, f.coeff i ∉ P := by
  classical
  letI : StrongNormalizationMonoid R := UniqueFactorizationMonoid.normalizationMonoid
  letI : NormalizedGCDMonoid R := UniqueFactorizationMonoid.toNormalizedGCDMonoid R
  obtain ⟨f, hf0, hfs⟩ := exists_ne_zero_aeval_eq_zero (R := R) (K := K) s
  refine ⟨f.primPart, ?_, ?_⟩
  · have hc : f.content ≠ 0 := by rwa [Ne, Polynomial.content_eq_zero_iff]
    have h1 : f.content • aeval s f.primPart = 0 := by
      rw [← hfs]
      conv_rhs => rw [Polynomial.eq_C_content_mul_primPart f]
      rw [map_mul, Polynomial.aeval_C, Algebra.smul_def]
    apply includeRight_injective (R := R) (K := K)
    rw [map_zero]
    have h2 := congrArg (Algebra.TensorProduct.includeRight : S →ₐ[R] K ⊗[R] S) h1
    rw [map_smul, map_zero, ← IsScalarTower.algebraMap_smul K, smul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact absurd h2 (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hc))
    · exact h2
  · by_contra hall
    push Not at hall
    obtain ⟨π, hπ⟩ := (IsPrincipalIdealRing.principal P).principal
    have hdvd : C π ∣ f.primPart := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have h := hall i
      rw [hπ, Ideal.submodule_span_eq, Ideal.mem_span_singleton'] at h
      obtain ⟨a, ha⟩ := h
      exact ⟨a, by rw [← ha, mul_comm]⟩
    have hu : IsUnit π :=
      (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp (Polynomial.isPrimitive_primPart f)) π hdvd
    apply hP
    rw [hπ, Ideal.submodule_span_eq, Ideal.span_singleton_eq_top]
    exact hu

private theorem isIntegral_quotient_map [IsPrincipalIdealRing R] [Module.Flat R S]
    [Module.Finite K (K ⊗[R] S)] (P : Ideal R) [P.IsMaximal] :
    Algebra.IsIntegral (R ⧸ P) (S ⧸ P.map (algebraMap R S)) := by
  classical
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  refine ⟨fun x => ?_⟩
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨f, hfs, i, hi⟩ := exists_aeval_eq_zero_not_forall_coeff_mem (R := R) (K := K) P
    (Ideal.IsMaximal.ne_top inferInstance) s
  have hne : f.map (Ideal.Quotient.mk P) ≠ 0 := by
    intro h0
    apply hi
    have h := congrArg (fun p : Polynomial (R ⧸ P) => p.coeff i) h0
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  have haeval : aeval (Ideal.Quotient.mk (P.map (algebraMap R S)) s)
      (f.map (Ideal.Quotient.mk P)) = 0 := by
    have h1 : f.map (Ideal.Quotient.mk P) = f.map (algebraMap R (R ⧸ P)) := rfl
    rw [h1, Polynomial.aeval_map_algebraMap]
    change aeval (Ideal.Quotient.mkₐ R (P.map (algebraMap R S)) s) f = 0
    rw [Polynomial.aeval_algHom_apply, hfs, map_zero]
  exact (isAlgebraic_iff_isIntegral.mp ⟨_, hne, haeval⟩)

end Helpers

namespace Algebra.QuasiFinite

/-- A flat finite-type algebra over a principal ideal domain whose generic
fibre is module-finite is quasi-finite. -/
public theorem of_flat_of_finiteType_of_moduleFinite_baseChange_fractionRing
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type w) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [Module.Flat R S]
    [Module.Finite K (K ⊗[R] S)] :
    Algebra.QuasiFinite R S := by
  classical
  refine ⟨fun P hP => ?_⟩
  by_cases hP0 : P = ⊥
  · subst hP0
    have hunit : ∀ y : R⁰, IsUnit (algebraMap R (⊥ : Ideal R).ResidueField (y : R)) := by
      intro y
      have hy : (y : R) ∈ (⊥ : Ideal R).primeCompl := by
        rw [Ideal.mem_primeCompl_iff, Ideal.mem_bot]
        exact nonZeroDivisors.ne_zero y.2
      rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime (⊥ : Ideal R))
        (⊥ : Ideal R).ResidueField]
      exact (IsLocalization.map_units (Localization.AtPrime (⊥ : Ideal R))
        (⟨(y : R), hy⟩ : (⊥ : Ideal R).primeCompl)).map _
    letI : Algebra K (⊥ : Ideal R).ResidueField := (IsLocalization.lift (M := R⁰) hunit).toAlgebra
    haveI : IsScalarTower R K (⊥ : Ideal R).ResidueField :=
      IsScalarTower.of_algebraMap_eq (fun r => (IsLocalization.lift_eq (M := R⁰) hunit r).symm)
    let e : (⊥ : Ideal R).ResidueField ⊗[K] (K ⊗[R] S) ≃ₐ[(⊥ : Ideal R).ResidueField]
        (⊥ : Ideal R).ResidueField ⊗[R] S :=
      Algebra.TensorProduct.cancelBaseChange R K _ _ S
    exact Module.Finite.of_surjective e.toLinearMap e.surjective
  · haveI : P.IsMaximal := IsPrime.to_maximal_ideal hP0
    letI : Field (R ⧸ P) := Ideal.Quotient.field P
    haveI : Algebra.IsIntegral (R ⧸ P) (S ⧸ P.map (algebraMap R S)) :=
      isIntegral_quotient_map (K := K) P
    haveI : Algebra.FiniteType R (S ⧸ P.map (algebraMap R S)) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R (P.map (algebraMap R S)))
        (Ideal.Quotient.mkₐ_surjective R _)
    haveI : Algebra.FiniteType (R ⧸ P) (S ⧸ P.map (algebraMap R S)) :=
      Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ P) _
    haveI : Module.Finite (R ⧸ P) (S ⧸ P.map (algebraMap R S)) := Algebra.IsIntegral.finite
    haveI : Module.Finite R (S ⧸ P.map (algebraMap R S)) := Module.Finite.trans (R ⧸ P) _
    let e₁ : (S ⧸ P.map (algebraMap R S)) ≃ₗ[R] (R ⧸ P) ⊗[R] S :=
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S P).toLinearEquiv.restrictScalars R
    haveI : Module.Finite R ((R ⧸ P) ⊗[R] S) :=
      Module.Finite.of_surjective e₁.toLinearMap e₁.surjective
    haveI : Module.Finite (R ⧸ P) ((R ⧸ P) ⊗[R] S) :=
      Module.Finite.of_restrictScalars_finite R (R ⧸ P) _
    let e₂ : P.ResidueField ⊗[R ⧸ P] ((R ⧸ P) ⊗[R] S) ≃ₐ[P.ResidueField]
        P.ResidueField ⊗[R] S :=
      Algebra.TensorProduct.cancelBaseChange R (R ⧸ P) _ _ S
    exact Module.Finite.of_surjective e₂.toLinearMap e₂.surjective

end Algebra.QuasiFinite
