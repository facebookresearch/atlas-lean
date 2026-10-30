/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.FractionalIdeal.Operations

/-!
# Dedekind domains: contain-is-divide and principal-product characterizations

ATLAS `NumberTheoryI`, Theorem 3.23, conditions (1), (5), and a corrected
nonvacuous form of (6): a domain `A` is Dedekind if and only if it is
noetherian with "to contain is to divide" for ideals, and if and only if
every nonzero ideal has a principal nonzero product with a suitable ideal.

The recorded target states (6) as `∀ I, ∃ J, (I * J).IsPrincipal`, which
is vacuous: `J = ⊥` makes the product principal for every `I`. The v1
formalization adds `I ≠ ⊥` and `I * J ≠ ⊥`. This module proves that
corrected, stronger criterion, rather than (6) as recorded without those
qualifiers.
Conditions (2) and (3) of Theorem 3.23 are already Mathlib iffs
(`IsDedekindDomainDvr` / `IsDedekindDomainInv`), condition (4) (prime
factorization of ideals) is not claimed here -- in v1 its
prime-factorization-implies-Dedekind direction is unproved in v1 --
and conditions (7) and (8) (quotients are principal ideal rings,
two-generator ideals) are not ported in this slice.
-/

@[expose] public section

open FractionalIdeal

open scoped nonZeroDivisors

variable {A : Type*} [CommRing A] [IsDomain A]

/-- A domain is a Dedekind domain if and only if it is noetherian and
"to contain is to divide" holds for ideals. -/
theorem isDedekindDomain_iff_contain_isDivide :
    IsDedekindDomain A ↔
      IsNoetherianRing A ∧ ∀ I J : Ideal A, I ∣ J ↔ J ≤ I := by
  constructor
  · intro _
    exact ⟨inferInstance, fun I J => Ideal.dvd_iff_le⟩
  · -- The Noetherian hypothesis is not needed here: invertibility
    -- of fractional ideals already forces it in Mathlib's proof.
    rintro ⟨-, hdvd⟩
    apply (isDedekindDomain_iff_mul_inv_cancel (K := FractionRing A)).mpr
    intro I hI
    rw [FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing A)]
    obtain ⟨a, J, ha, hI_eq⟩ :=
      FractionalIdeal.exists_eq_spanSingleton_mul I
    have ha_map : (algebraMap A (FractionRing A) a)⁻¹ ≠ 0 := by
      simp [ha]
    have hspan_unit : IsUnit (FractionalIdeal.spanSingleton A⁰
        (algebraMap A (FractionRing A) a)⁻¹) :=
      (FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing A)).mp
        (FractionalIdeal.spanSingleton_mul_inv (FractionRing A) ha_map)
    have hJ_ne : J ≠ ⊥ := by
      intro heq
      apply hI
      rw [hI_eq, heq]
      simp
    obtain ⟨x, hxJ, hx0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot hJ_ne
    have hle : Ideal.span {x} ≤ J :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxJ)
    obtain ⟨K, hK⟩ := (hdvd J (Ideal.span {x})).mpr hle
    have hfrac : (↑J : FractionalIdeal A⁰ (FractionRing A)) * ↑K =
        ↑(Ideal.span {x}) := by
      rw [← FractionalIdeal.coeIdeal_mul, hK]
    have hinv : (↑(Ideal.span {x}) :
        FractionalIdeal A⁰ (FractionRing A)) *
        (↑(Ideal.span {x}))⁻¹ = 1 :=
      FractionalIdeal.coe_ideal_span_singleton_mul_inv (FractionRing A) hx0
    have hJ_unit : IsUnit (↑J : FractionalIdeal A⁰ (FractionRing A)) :=
      (FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing A)).mp
        ((FractionalIdeal.mul_inv_cancel_iff (FractionRing A)).mpr
          ⟨↑K * (↑(Ideal.span {x}))⁻¹, by
            rw [← mul_assoc, hfrac, hinv]⟩)
    rw [hI_eq]
    exact IsUnit.mul hspan_unit hJ_unit

/-- The corrected nonvacuous form of Theorem 3.23(6): a domain is Dedekind
if and only if every nonzero ideal has a principal nonzero product with a
suitable ideal. The recorded target omits both nonzero qualifiers. -/
theorem isDedekindDomain_iff_principalProduct :
    IsDedekindDomain A ↔
      ∀ I : Ideal A, I ≠ ⊥ →
        ∃ J : Ideal A, (I * J).IsPrincipal ∧ I * J ≠ ⊥ := by
  constructor
  · intro _ I hI
    obtain ⟨a, haI, ha0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot hI
    have ha_le : Ideal.span {a} ≤ I :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr haI)
    obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr ha_le
    refine ⟨J, ?_, ?_⟩
    · rw [← hJ]
      exact ⟨⟨a, rfl⟩⟩
    · rw [← hJ]
      rwa [Ne, Ideal.span_singleton_eq_bot]
  · intro h6
    apply (isDedekindDomain_iff_mul_inv_cancel (K := FractionRing A)).mpr
    intro I hI
    rw [FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing A)]
    have hI0 : I ≠ 0 := by
      rwa [FractionalIdeal.bot_eq_zero] at hI
    obtain ⟨a, aI, ha, hI_eq⟩ :=
      FractionalIdeal.exists_eq_spanSingleton_mul I
    have haI_ne : aI ≠ ⊥ := by
      have hne := FractionalIdeal.ideal_factor_ne_zero hI0 hI_eq
      rwa [ne_eq, Ideal.zero_eq_bot] at hne
    obtain ⟨J, hIJ_princ, hIJ_ne⟩ := h6 aI haI_ne
    obtain ⟨⟨c, hc⟩⟩ := hIJ_princ
    have hc0 : c ≠ 0 := by
      intro h
      apply hIJ_ne
      rw [hc, h]
      simp
    have h_inv := FractionalIdeal.coe_ideal_span_singleton_mul_inv
      (FractionRing A) hc0
    have hcoe : (↑(aI * J) :
        FractionalIdeal A⁰ (FractionRing A)) = ↑(Ideal.span {c}) := by
      exact_mod_cast congrArg _ hc
    rw [FractionalIdeal.coeIdeal_mul] at hcoe
    rw [← hcoe] at h_inv
    have haIJ_unit : IsUnit (↑aI * ↑J :
        FractionalIdeal A⁰ (FractionRing A)) :=
      (FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing A)).mp h_inv
    have haI_unit : IsUnit (↑aI :
        FractionalIdeal A⁰ (FractionRing A)) := by
      obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp haIJ_unit
      refine isUnit_iff_exists_inv.mpr ⟨↑J * y, ?_⟩
      rw [← mul_assoc, hy]
    have ha_inv_ne : (algebraMap A (FractionRing A) a)⁻¹ ≠ 0 := by
      simp [ha]
    have hspan_unit : IsUnit (FractionalIdeal.spanSingleton A⁰
        (algebraMap A (FractionRing A) a)⁻¹) :=
      (FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing A)).mp
        (FractionalIdeal.spanSingleton_mul_inv (FractionRing A) ha_inv_ne)
    rw [hI_eq]
    exact IsUnit.mul hspan_unit haI_unit

/-- Theorem 3.23, conditions (1), (5), and the corrected nonvacuous form
of (6): the three Dedekind-domain characterizations are equivalent. -/
theorem isDedekindDomain_tfae_contain_isDivide_principalProduct :
    List.TFAE
      [IsDedekindDomain A,
       IsNoetherianRing A ∧ ∀ I J : Ideal A, I ∣ J ↔ J ≤ I,
       ∀ I : Ideal A, I ≠ ⊥ →
         ∃ J : Ideal A, (I * J).IsPrincipal ∧ I * J ≠ ⊥] := by
  tfae_have 1 ↔ 2 := isDedekindDomain_iff_contain_isDivide
  tfae_have 1 ↔ 3 := isDedekindDomain_iff_principalProduct
  tfae_finish
