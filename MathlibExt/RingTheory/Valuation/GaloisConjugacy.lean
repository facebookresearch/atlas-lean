/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ValuationSubring_exists_algEquiv_comap_eq_of_isGalois.lean`
and
`P2M/Sol/S_ValuationSubring_exists_algEquiv_comap_eq_of_isGalois.lean`
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

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.Valuation.LocalSubring

@[expose] public section

set_option autoImplicit false

open IsLocalRing
open IsDedekindDomain


private theorem eq_valuationSubringAtPrime {C K : Type*} [CommRing C] [IsDedekindDomain C] [Field K]
  [Algebra C K]
    [IsFractionRing C K] (v : HeightOneSpectrum C) (D : ValuationSubring K)
    (hCD : ∀ c : C, algebraMap C K c ∈ D)
    (hcen : ∀ c : C, algebraMap C K c ∈ D.nonunits ↔ c ∈ v.asIdeal) :
    D = HeightOneSpectrum.valuationSubringAtPrime K v := by
  classical
  have hsD : ∀ s : C, s ∉ v.asIdeal → (algebraMap C K s)⁻¹ ∈ D := by
    intro s hs
    have h : algebraMap C K s ∉ D.nonunits := fun h => hs ((hcen s).1 h)
    rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at h
    exact h.2

  have hOD : (HeightOneSpectrum.valuationSubringAtPrime K v).toSubring ≤ D.toSubring := by
    intro x hx
    rw [HeightOneSpectrum.valuationSubringAtPrime_toSubring] at hx
    obtain ⟨a, s, hs, rfl⟩ := hx
    exact mul_mem (hCD a) (hsD s hs)

  have hloc : IsLocalHom (Subring.inclusion hOD) := by
    constructor
    intro x0 hx0
    suffices h : IsUnit (⟨x0.1, x0.2⟩ : ↥(HeightOneSpectrum.valuationSubringAtPrime K v)) by exact h
    have hx : IsUnit (⟨(Subring.inclusion hOD x0).1, (Subring.inclusion hOD x0).2⟩ : ↥D) := by exact
      hx0
    obtain ⟨⟨a, s⟩, hmk⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl
      (⟨x0.1, x0.2⟩ : ↥(HeightOneSpectrum.valuationSubringAtPrime K v))
    rw [← hmk, IsLocalization.AtPrime.isUnit_mk'_iff (↥(HeightOneSpectrum.valuationSubringAtPrime K
      v)) v.asIdeal a s]
    by_contra ha
    have ha' : a ∈ v.asIdeal := by simpa [Ideal.primeCompl] using ha

    have hspec := IsLocalization.mk'_spec (↥(HeightOneSpectrum.valuationSubringAtPrime K v)) a s
    have hK : ((IsLocalization.mk' (↥(HeightOneSpectrum.valuationSubringAtPrime K v)) a s :
        ↥(HeightOneSpectrum.valuationSubringAtPrime K v)) : K) * algebraMap C K (s : C) = algebraMap
          C K a := by
      have h := congrArg (algebraMap (↥(HeightOneSpectrum.valuationSubringAtPrime K v)) K) hspec
      rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
      exact h
    have hs0 : algebraMap C K (s : C) ≠ 0 := by
      intro h0
      have : (s : C) = 0 := (IsFractionRing.injective C K) (by rw [h0, map_zero])
      exact s.2 (by rw [this]; exact v.asIdeal.zero_mem)
    have hxK : ((IsLocalization.mk' (↥(HeightOneSpectrum.valuationSubringAtPrime K v)) a s :
        ↥(HeightOneSpectrum.valuationSubringAtPrime K v)) : K) = algebraMap C K a * (algebraMap C K
          (s : C))⁻¹ := by
      rw [← hK, mul_assoc, mul_inv_cancel₀ hs0, mul_one]

    have hnu : algebraMap C K a * (algebraMap C K (s : C))⁻¹ ∈ D.nonunits := by
      rw [ValuationSubring.mem_nonunits_iff, map_mul]
      have h1 : D.valuation (algebraMap C K a) < 1 := (ValuationSubring.mem_nonunits_iff _).1 ((hcen
        a).2 ha')
      have h2 : D.valuation ((algebraMap C K (s : C))⁻¹) ≤ 1 := (D.valuation_le_one_iff _).2 (hsD s
        s.2)
      calc D.valuation (algebraMap C K a) * D.valuation ((algebraMap C K (s : C))⁻¹)
          ≤ D.valuation (algebraMap C K a) * 1 := mul_le_mul_right h2 _
        _ = D.valuation (algebraMap C K a) := mul_one _
        _ < 1 := h1

    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.1 hx
    have hyK : ((⟨x0.1, x0.2⟩ : ↥(HeightOneSpectrum.valuationSubringAtPrime K v)) : K) * (y : K) = 1
      := by
      have h := congrArg Subtype.val hy
      simpa using h
    rw [← hmk, hxK] at hyK
    have hne : algebraMap C K a * (algebraMap C K (s : C))⁻¹ ≠ 0 := left_ne_zero_of_mul_eq_one hyK
    have hinv : (algebraMap C K a * (algebraMap C K (s : C))⁻¹)⁻¹ ∈ D := by
      rw [(mul_eq_one_iff_inv_eq₀ hne).1 hyK]; exact y.2
    rcases (ValuationSubring.mem_nonunits_iff_or _).1 hnu with h0 | h0
    · exact hne h0
    · exact h0 hinv
  have hle : (HeightOneSpectrum.valuationSubringAtPrime K v).toLocalSubring ≤ D.toLocalSubring :=
    ⟨hOD, hloc⟩
  have hge := (HeightOneSpectrum.valuationSubringAtPrime K v).isMax_toLocalSubring hle
  exact (ValuationSubring.toLocalSubring_injective (le_antisymm hle hge)).symm

private theorem exists_centre {C K : Type*} [CommRing C] [Field K] [Algebra C K]
    (D : ValuationSubring K) (hCD : ∀ c : C, algebraMap C K c ∈ D) :
    ∃ P : Ideal C, P.IsPrime ∧ ∀ c : C, c ∈ P ↔ algebraMap C K c ∈ D.nonunits := by
  let f : C →+* ↥D :=
    { toFun := fun c => ⟨algebraMap C K c, hCD c⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ a b) }
  refine ⟨(IsLocalRing.maximalIdeal ↥D).comap f, Ideal.comap_isPrime f _, fun c => ?_⟩
  rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, ValuationSubring.mem_nonunits_iff]
  exact Iff.rfl

private theorem mem_nonunits_comap_iff {K L : Type*} [Field K] [Field L] (A : ValuationSubring L) (f
  : K →+* L)
    (x : K) : x ∈ (A.comap f).nonunits ↔ f x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap,
    map_inv₀, map_eq_zero]

/-- In a finite Galois extension, any two valuation subrings lying over the
same discrete valuation subring of the base field are conjugate by a
base-field automorphism of the extension. -/
public theorem ValuationSubring.exists_algEquiv_comap_eq_of_isGalois
    {E K : Type*} [Field E] [Field K] [Algebra E K] [FiniteDimensional E K] [IsGalois E K]
    (V : ValuationSubring E) [IsDiscreteValuationRing ↥V]
    (B B' : ValuationSubring K)
    (hB : ∀ x : E, algebraMap E K x ∈ B ↔ x ∈ V) (hB' : ∀ x : E, algebraMap E K x ∈ B' ↔ x ∈ V) :
    ∃ σ : K ≃ₐ[E] K, B' = B.comap σ.toAlgHom.toRingHom := by
  classical

  letI algVK : Algebra ↥V K := ((algebraMap E K).comp (algebraMap ↥V E)).toAlgebra
  haveI : IsScalarTower ↥V E K := IsScalarTower.of_algebraMap_eq fun _ => rfl

  haveI : Algebra.IsSeparable E K := inferInstance
  haveI : IsDedekindDomain ↥(integralClosure ↥V K) := IsIntegralClosure.isDedekindDomain ↥V E K _
  haveI : IsFractionRing ↥(integralClosure ↥V K) K :=
    IsIntegralClosure.isFractionRing_of_finite_extension ↥V E K _
  letI := IsIntegralClosure.MulSemiringAction ↥V E K ↥(integralClosure ↥V K)
  haveI hinv : Algebra.IsInvariant ↥V ↥(integralClosure ↥V K) (K ≃ₐ[E] K) :=
    Algebra.isInvariant_of_isGalois ↥V E K ↥(integralClosure ↥V K)
  haveI : SMulCommClass (K ≃ₐ[E] K) ↥V ↥(integralClosure ↥V K) :=
    ⟨fun g a c => by
      change galRestrict ↥V E K ↥(integralClosure ↥V K) g (a • c) = a • galRestrict ↥V E K
        ↥(integralClosure ↥V K) g c
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]⟩

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥V
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hϖu : ¬ IsUnit ϖ := hϖ.not_isUnit

  have hgen : ∀ (D : ValuationSubring K), (∀ x : E, algebraMap E K x ∈ D ↔ x ∈ V) →
      (∀ c : ↥(integralClosure ↥V K), algebraMap _ K c ∈ D) ∧
      (∀ x : ↥V, algebraMap ↥V K x ∈ D.nonunits ↔ x ∈ IsLocalRing.maximalIdeal ↥V) := by
    intro D hD
    refine ⟨fun c => ?_, fun x => ?_⟩
    ·
      have hc : IsIntegral ↥V (algebraMap _ K c) := c.2
      let fV : ↥V →+* ↥D :=
        { toFun := fun x => ⟨algebraMap E K x, (hD x).2 x.2⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun a b => Subtype.ext (by simp)
          map_zero' := Subtype.ext (by simp)
          map_add' := fun a b => Subtype.ext (by simp) }
      have hcD : IsIntegral ↥D (algebraMap _ K c) :=
        hc.map_of_comp_eq fV (RingHom.id K) (by ext x; rfl)
      obtain ⟨d, hd⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥D) (K := K)).mp hcD
      rw [← hd]; exact d.2
    ·
      constructor
      · intro hx
        by_contra hxu
        have hxu' : IsUnit x := by
          rwa [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff, not_not] at hxu
        obtain ⟨u, rfl⟩ := hxu'
        rcases (ValuationSubring.mem_nonunits_iff_or _).1 hx with h0 | hinv
        · exact (u.ne_zero) (by
            have : algebraMap ↥V E (u : ↥V) = 0 :=
              (algebraMap E K).injective (by rw [map_zero]; exact h0)
            exact Subtype.ext (by simpa using this))
        · apply hinv
          have : (algebraMap ↥V K (u : ↥V))⁻¹ = algebraMap E K (((u⁻¹ : (↥V)ˣ) : ↥V) : E) := by
            rw [eq_comm, ← mul_eq_one_iff_eq_inv₀]
            · show algebraMap E K (((u⁻¹ : (↥V)ˣ) : ↥V) : E) * algebraMap E K ((u : ↥V) : E) = 1
              rw [← map_mul, ← Subring.coe_mul]
              simp
            · intro h0
              have : algebraMap ↥V E (u : ↥V) = 0 :=
                (algebraMap E K).injective (by rw [map_zero]; exact h0)
              exact u.ne_zero (Subtype.ext (by simpa using this))
          rw [this]
          exact (hD _).2 (Subtype.mem _)
      · intro hx
        rw [ValuationSubring.mem_nonunits_iff_or]
        by_cases hx0 : (x : E) = 0
        · left
          rw [show x = 0 from Subtype.ext hx0, map_zero]
        · right
          intro hinv
          have hmem : (x : E)⁻¹ ∈ V := (hD _).1 (by rw [map_inv₀]; exact hinv)
          have hu : IsUnit x :=
            IsUnit.of_mul_eq_one ⟨(x : E)⁻¹, hmem⟩ (Subtype.ext (by simp [mul_inv_cancel₀ hx0]))
          exact hx hu
  have hVCinj : Function.Injective (algebraMap ↥V ↥(integralClosure ↥V K)) := by
    intro a b hab
    have h := congrArg (algebraMap ↥(integralClosure ↥V K) K) hab
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
    exact Subtype.ext ((algebraMap E K).injective h)

  have hcen : ∀ (D : ValuationSubring K), (∀ x : E, algebraMap E K x ∈ D ↔ x ∈ V) →
      ∃ v : IsDedekindDomain.HeightOneSpectrum ↥(integralClosure ↥V K),
        (∀ c : ↥(integralClosure ↥V K), algebraMap _ K c ∈ D.nonunits ↔ c ∈ v.asIdeal) ∧
        v.asIdeal.under ↥V = IsLocalRing.maximalIdeal ↥V ∧
        D = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v := by
    intro D hD
    obtain ⟨hCD, hVD⟩ := hgen D hD
    obtain ⟨P, hPp, hP⟩ := exists_centre D hCD
    have hPne : P ≠ ⊥ := by
      intro hbot
      have h1 : algebraMap ↥V ↥(integralClosure ↥V K) ϖ ∈ P := by
        rw [hP, ← IsScalarTower.algebraMap_apply]
        exact (hVD ϖ).2 ((IsLocalRing.mem_maximalIdeal _).2 hϖu)
      rw [hbot, Ideal.mem_bot] at h1
      exact hϖ0 (hVCinj (by rw [h1, map_zero]))
    let v : IsDedekindDomain.HeightOneSpectrum ↥(integralClosure ↥V K) := ⟨P, hPp, hPne⟩
    have hv : ∀ c : ↥(integralClosure ↥V K), algebraMap _ K c ∈ D.nonunits ↔ c ∈ v.asIdeal := fun c
      => (hP c).symm
    refine ⟨v, hv, ?_, eq_valuationSubringAtPrime v D hCD hv⟩
    ext x
    rw [Ideal.under_def, Ideal.mem_comap, ← hv, ← IsScalarTower.algebraMap_apply]
    exact hVD x
  obtain ⟨v, hv, hvV, hBv⟩ := hcen B hB
  obtain ⟨v', hv', hv'V, hB'v⟩ := hcen B' hB'

  haveI := v.isPrime
  haveI := v'.isPrime
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq ↥V ↥(integralClosure ↥V K) (K ≃ₐ[E]
    K)
    v.asIdeal v'.asIdeal (hvV.trans hv'V.symm)
  refine ⟨g⁻¹, ?_⟩

  have hD : ∀ x : E, algebraMap E K x ∈ B.comap (g⁻¹ : K ≃ₐ[E] K).toAlgHom.toRingHom ↔ x ∈ V := by
    intro x
    rw [ValuationSubring.mem_comap]
    show (g⁻¹ : K ≃ₐ[E] K) (algebraMap E K x) ∈ B ↔ x ∈ V
    rw [AlgEquiv.commutes]
    exact hB x
  obtain ⟨w, hw, -, hDw⟩ := hcen _ hD
  have hsmul : ∀ (τ : K ≃ₐ[E] K) (c : ↥(integralClosure ↥V K)), ((τ • c : ↥(integralClosure ↥V K)) :
    K) = τ (c : K) := fun τ c =>
    algebraMap_galRestrict_apply (A := ↥V) (K := E) (L := K) τ c
  have hwv' : w = v' := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    ext c
    rw [← hw, mem_nonunits_comap_iff, hg, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← hv]
    show (g⁻¹ : K ≃ₐ[E] K) (c : K) ∈ B.nonunits ↔ (((g⁻¹ • c) : ↥(integralClosure ↥V K)) : K) ∈
      B.nonunits
    rw [hsmul]
  rw [hB'v, hDw, hwv']
