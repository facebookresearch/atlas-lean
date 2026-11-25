/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_Smooth_of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField.lean`
and
`P2M/Sol/S_Algebra_Smooth_of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField.lean`
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

public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Unramified.LocalStructure

@[expose] public section

universe u v

open IsLocalRing Polynomial

attribute [local instance] Ideal.Quotient.field

private theorem formallySmooth_of_maximalIdeal_eq_span_of_isSeparable_residueField
    (K₀ : Type u) [Field K₀] (𝒪 : Type v) [CommRing 𝒪] [IsLocalRing 𝒪]
    [IsDomain 𝒪] [IsNoetherianRing 𝒪]
    [Algebra K₀ 𝒪] [Algebra.EssFiniteType K₀ 𝒪]
    (u : 𝒪) (hu0 : u ≠ 0) (hu : maximalIdeal 𝒪 = Ideal.span {u})
    [Algebra.IsAlgebraic K₀ (ResidueField 𝒪)]
    [Algebra.IsSeparable K₀ (ResidueField 𝒪)] :
    Algebra.FormallySmooth K₀ 𝒪 := by
  classical

  let A : Subalgebra K₀ 𝒪 := Algebra.EssFiniteType.subalgebra K₀ 𝒪
  let M : Submonoid A := Algebra.EssFiniteType.submonoid K₀ 𝒪
  haveI hlocM : IsLocalization M 𝒪 := Algebra.EssFiniteType.isLocalization K₀ 𝒪
  obtain ⟨⟨a, sM⟩, has⟩ := IsLocalization.surj M u

  have hsunit : IsUnit (algebraMap A 𝒪 (sM : A)) := IsLocalization.map_units 𝒪 sM
  have hspan : maximalIdeal 𝒪 = Ideal.span {algebraMap A 𝒪 a} := by
    rw [hu, ← has]
    exact (Ideal.span_singleton_mul_right_unit hsunit u).symm
  have ha𝔪 : algebraMap A 𝒪 a ∈ maximalIdeal 𝒪 := hspan ▸ Ideal.mem_span_singleton_self _
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hu0
    have : u * algebraMap A 𝒪 (sM : A) = 0 := by rw [has, map_zero]
    exact (hsunit.mul_left_eq_zero).mp this

  let Q : Ideal A := (maximalIdeal 𝒪).comap (algebraMap A 𝒪)
  haveI hQprime : Q.IsPrime := Ideal.IsPrime.comap _
  have haQ : a ∈ Q := ha𝔪
  have hMQ : M = Q.primeCompl := by
    ext x
    change IsUnit (algebraMap A 𝒪 x) ↔ x ∉ Q
    change _ ↔ algebraMap A 𝒪 x ∉ maximalIdeal 𝒪
    rw [mem_maximalIdeal, mem_nonunits_iff, not_not]
  haveI hlocQ : IsLocalization.AtPrime 𝒪 Q := by
    change IsLocalization Q.primeCompl 𝒪
    rw [← hMQ]; exact hlocM

  let eA : 𝒪 ≃ₐ[A] Localization.AtPrime Q := IsLocalization.algEquiv Q.primeCompl 𝒪
    (Localization.AtPrime Q)
  let eK : 𝒪 ≃ₐ[K₀] Localization.AtPrime Q := eA.restrictScalars K₀

  have hQtop : Q ≠ ⊤ := hQprime.ne_top
  have ha : Transcendental K₀ a := by
    intro halg
    have hint : IsIntegral K₀ a := halg.isIntegral
    have hc : (minpoly K₀ a).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint ha0
    have h := minpoly.aeval K₀ a
    rw [← (minpoly K₀ a).X_mul_divX_add, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
      at h
    have key : algebraMap K₀ A ((minpoly K₀ a).coeff 0) = -(a * Polynomial.aeval a (minpoly K₀
      a).divX) :=
      eq_neg_of_add_eq_zero_right h
    exact hQtop (Q.eq_top_of_isUnit_mem (key ▸ Q.neg_mem (Q.mul_mem_right _ haQ)) ((IsUnit.mk0 _
      hc).map _))

  letI alg : Algebra K₀[X] A := (Polynomial.aeval a : K₀[X] →ₐ[K₀] A).toRingHom.toAlgebra
  have halg : ∀ f : K₀[X], algebraMap K₀[X] A f = Polynomial.aeval a f := fun _ => rfl
  haveI : IsScalarTower K₀ K₀[X] A :=
    IsScalarTower.of_algebraMap_eq fun k => ((Polynomial.aeval a).commutes k).symm
  haveI : IsScalarTower K₀ K₀[X] (Localization.AtPrime Q) :=
    IsScalarTower.of_algebraMap_eq fun k => by
      rw [IsScalarTower.algebraMap_apply K₀ A (Localization.AtPrime Q),
        IsScalarTower.algebraMap_apply K₀[X] A (Localization.AtPrime Q),
        IsScalarTower.algebraMap_apply K₀ K₀[X] A]
  haveI : Module.IsTorsionFree K₀[X] A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (transcendental_iff_injective.mp ha)
  haveI : Module.Flat K₀[X] A := inferInstance
  haveI : Algebra.FiniteType K₀[X] A := Algebra.FiniteType.of_restrictScalars_finiteType K₀ K₀[X] A
  haveI : Algebra.FinitePresentation K₀[X] A := (Algebra.FinitePresentation.of_finiteType).mp ‹_›

  let ι : (A ⧸ Q) →ₐ[K₀] ResidueField 𝒪 :=
    Ideal.quotientMapₐ (maximalIdeal 𝒪) (IsScalarTower.toAlgHom K₀ A 𝒪) le_rfl
  have hι : Function.Injective ι := Ideal.quotientMap_injective
  haveI : Algebra.IsAlgebraic K₀ (A ⧸ Q) := Algebra.IsAlgebraic.of_injective ι hι
  haveI : Algebra.IsIntegral K₀ (A ⧸ Q) := Algebra.IsAlgebraic.isIntegral
  haveI hQmax : Q.IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (isField_of_isIntegral_of_isField' (Field.toIsField K₀))
  haveI : Algebra.IsSeparable K₀ (A ⧸ Q) := Algebra.IsSeparable.of_algHom _ _ ι

  have hXp : (X : K₀[X]) ∈ Q.under K₀[X] := by
    change algebraMap K₀[X] A X ∈ Q
    rwa [halg, Polynomial.aeval_X]
  haveI : (Q.under K₀[X]).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance fun h =>
      Polynomial.X_ne_zero ((Submodule.eq_bot_iff _).mp h X hXp)
  letI := Localization.AtPrime.algebraOfLiesOver (Q.under K₀[X]) Q
  haveI : Algebra.IsSeparable (K₀[X] ⧸ Q.under K₀[X]) (↥A ⧸ Q) :=
    Algebra.isSeparable_tower_top_of_isSeparable K₀ (K₀[X] ⧸ Q.under K₀[X]) (↥A ⧸ Q)

  haveI : Algebra.IsSeparable (Q.under K₀[X]).ResidueField Q.ResidueField :=
    Algebra.isSeparable_residueField_iff.mpr inferInstance
  haveI : Algebra.IsUnramifiedAt K₀[X] Q := by
    rw [Algebra.isUnramifiedAt_iff_map_eq (p := Q.under K₀[X])]
    refine ⟨inferInstance, le_antisymm ?_ ?_⟩
    · refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply K₀[X] A (Localization.AtPrime Q)]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q _).mpr hf
    · intro z hz

      have hz' : eA.symm z ∈ maximalIdeal 𝒪 := by
        rw [mem_maximalIdeal, mem_nonunits_iff] at hz ⊢
        exact fun h => hz (by simpa using h.map eA)
      rw [hspan, Ideal.mem_span_singleton'] at hz'
      obtain ⟨r, hr⟩ := hz'
      have hz'' : z = eA r * algebraMap K₀[X] (Localization.AtPrime Q) X := by
        rw [IsScalarTower.algebraMap_apply K₀[X] A (Localization.AtPrime Q), halg,
          Polynomial.aeval_X,
          ← eA.commutes a, ← map_mul, hr, AlgEquiv.apply_symm_apply]
      rw [hz'']
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hXp)

  haveI : Algebra.IsEtaleAt K₀[X] Q := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat Q
  haveI : Algebra.FormallySmooth K₀[X] (Localization.AtPrime Q) := inferInstance
  haveI : Algebra.FormallySmooth K₀ (Localization.AtPrime Q) :=
    Algebra.FormallySmooth.comp K₀ K₀[X] (Localization.AtPrime Q)
  exact Algebra.FormallySmooth.of_equiv eK.symm

private theorem formallySmooth_of_maximalIdeal_eq_span_of_perfectField
    (K : Type u) [Field K] [PerfectField K] (𝒪 : Type v) [CommRing 𝒪]
    [IsLocalRing 𝒪] [IsDomain 𝒪] [IsNoetherianRing 𝒪]
    [Algebra K 𝒪] [Algebra.EssFiniteType K 𝒪]
    (u : 𝒪) (hu0 : u ≠ 0) (hu : maximalIdeal 𝒪 = Ideal.span {u}) :
    Algebra.FormallySmooth K 𝒪 := by
  classical

  haveI : Algebra.EssFiniteType K (ResidueField 𝒪) :=
    Algebra.EssFiniteType.comp K 𝒪 (ResidueField 𝒪)
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K
    (ResidueField 𝒪)
  have hinj : Function.Injective (MvPolynomial.aeval (R := K) ((↑) : s → ResidueField 𝒪)) :=
    algebraicIndependent_iff_injective_aeval.1 hs.1

  choose t ht using fun x : s => IsLocalRing.residue_surjective (R := 𝒪) (x : ResidueField 𝒪)
  let P := MvPolynomial s K
  let φ : P →ₐ[K] 𝒪 := MvPolynomial.aeval t
  have hφres : ∀ f : P, IsLocalRing.residue 𝒪 (φ f) = MvPolynomial.aeval ((↑) : s → ResidueField 𝒪)
    f := by
    intro f
    have hcomp : ((IsScalarTower.toAlgHom K 𝒪 (ResidueField 𝒪)).comp φ) =
        MvPolynomial.aeval ((↑) : s → ResidueField 𝒪) := by
      refine MvPolynomial.algHom_ext fun i => ?_
      simp [φ, ht i]
    exact congrArg (fun g : P →ₐ[K] ResidueField 𝒪 => g f) hcomp

  have hunit : ∀ f : P, f ≠ 0 → IsUnit (φ f) := by
    intro f hf
    by_contra h
    have hmem : φ f ∈ maximalIdeal 𝒪 := h
    have h0 : IsLocalRing.residue 𝒪 (φ f) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [hφres] at h0
    exact hf (hinj (by rw [h0, map_zero]))

  let K₀ := FractionRing P
  let ψ : K₀ →ₐ[K] 𝒪 := IsLocalization.liftAlgHom (M := nonZeroDivisors P) (f := φ)
    (fun y => hunit y.1 (nonZeroDivisors.ne_zero y.2))
  letI : Algebra K₀ 𝒪 := ψ.toRingHom.toAlgebra
  have hψ : ∀ z : K₀, algebraMap K₀ 𝒪 z = ψ z := fun _ => rfl
  haveI : IsScalarTower K K₀ 𝒪 := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hψ, ψ.commutes]
  letI : Algebra P 𝒪 := φ.toRingHom.toAlgebra
  have hφ : ∀ f : P, algebraMap P 𝒪 f = φ f := fun _ => rfl
  haveI : IsScalarTower P K₀ 𝒪 := IsScalarTower.of_algebraMap_eq fun f => by
    rw [hψ, hφ]
    change φ f = IsLocalization.lift (M := nonZeroDivisors P) _ (algebraMap P K₀ f)
    rw [IsLocalization.lift_eq]
    rfl

  haveI : Algebra.FormallySmooth P K₀ := Algebra.FormallySmooth.of_isLocalization (Rₘ := K₀)
    (nonZeroDivisors P)
  haveI : Algebra.FormallySmooth K K₀ := Algebra.FormallySmooth.comp K P K₀
  haveI : Algebra.EssFiniteType K₀ 𝒪 := Algebra.EssFiniteType.of_comp K K₀ 𝒪

  let F : IntermediateField K (ResidueField 𝒪) := IntermediateField.adjoin K (Set.range ((↑) : s →
    ResidueField 𝒪))
  let e : K₀ ≃ₐ[K] F := hs.1.aevalEquivField
  have hrange : (Set.range ((↑) : s → ResidueField 𝒪)) = (s : Set (ResidueField 𝒪)) := by
    ext x; simp
  haveI : Algebra.IsSeparable F (ResidueField 𝒪) := by
    have : F = IntermediateField.adjoin K (s : Set (ResidueField 𝒪)) := by rw [← hrange]
    rw [this]; exact hsep
  have hcompat : (algebraMap K₀ (ResidueField 𝒪)).comp (e.symm.toRingEquiv : F →+* K₀) =
      (RingEquiv.refl (ResidueField 𝒪) : ResidueField 𝒪 →+* ResidueField 𝒪).comp (algebraMap F
        (ResidueField 𝒪)) := by

    have key : (algebraMap K₀ (ResidueField 𝒪)) = (algebraMap F (ResidueField 𝒪)).comp
      (e.toRingEquiv : K₀ →+* F) := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors P) ?_
      ext f
      · simp only [RingHom.coe_comp, Function.comp_apply]
        rw [IsScalarTower.algebraMap_apply K₀ 𝒪 (ResidueField 𝒪), ← IsScalarTower.algebraMap_apply
          P K₀ 𝒪]
        change IsLocalRing.residue 𝒪 (φ (MvPolynomial.C f)) = _
        rw [hφres]
        change MvPolynomial.aeval _ (MvPolynomial.C f) =
          ((e (algebraMap P K₀ (MvPolynomial.C f)) : F) : ResidueField 𝒪)
        rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
      · simp only [RingHom.coe_comp, Function.comp_apply]
        rw [IsScalarTower.algebraMap_apply K₀ 𝒪 (ResidueField 𝒪), ← IsScalarTower.algebraMap_apply
          P K₀ 𝒪]
        change IsLocalRing.residue 𝒪 (φ (MvPolynomial.X _)) = _
        rw [hφres]
        change MvPolynomial.aeval _ (MvPolynomial.X _) =
          ((e (algebraMap P K₀ (MvPolynomial.X _)) : F) : ResidueField 𝒪)
        rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
    rw [key]
    ext x
    simp
  haveI : Algebra.IsSeparable K₀ (ResidueField 𝒪) :=
    Algebra.IsSeparable.of_equiv_equiv (e.symm.toRingEquiv : F ≃+* K₀) (RingEquiv.refl
      (ResidueField 𝒪)) hcompat
  haveI : Algebra.IsAlgebraic K₀ (ResidueField 𝒪) := Algebra.IsSeparable.isAlgebraic _ _

  haveI := formallySmooth_of_maximalIdeal_eq_span_of_isSeparable_residueField K₀ 𝒪 u hu0 hu
  exact Algebra.FormallySmooth.comp K K₀ 𝒪

/-- A finite-type normal domain of Krull dimension at most one over a
perfect field is smooth over that field. -/
public theorem Algebra.Smooth.of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField
    (k : Type u) [Field k] [PerfectField k] (B : Type v) [CommRing B]
    [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] [IsIntegrallyClosed B] [Ring.KrullDimLE 1 B] :
    Algebra.Smooth k B := by
  classical
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  haveI hfp : Algebra.FinitePresentation k B := (Algebra.FinitePresentation.of_finiteType).mp
    inferInstance
  suffices hfs : Algebra.FormallySmooth k B from ⟨hfs, hfp⟩
  by_cases hB : IsField B
  · letI : Field B := hB.toField
    haveI : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B
    haveI : Algebra.IsSeparable k B := Algebra.IsAlgebraic.isSeparable_of_perfectField
    haveI : Algebra.FormallyEtale k B := Algebra.FormallyEtale.of_isSeparable k B
    infer_instance
  · haveI : Ring.DimensionLEOne B := ⟨fun hp hpp => hpp.isMaximal_of_ne_bot hp⟩
    haveI : IsDedekindDomain B := (isDedekindDomain_iff B (FractionRing B)).mpr
      ⟨inferInstance, inferInstance, inferInstance, fun hx => (isIntegrallyClosed_iff (FractionRing
        B)).mp inferInstance hx⟩

    have hmax : ∀ p : PrimeSpectrum B, p.asIdeal.IsMaximal → p ∈ Algebra.smoothLocus k B := by
      intro p hp
      change Algebra.FormallySmooth k (Localization.AtPrime p.asIdeal)
      have hne : p.asIdeal ≠ ⊥ := by
        intro h
        apply hB
        rw [Ring.isField_iff_maximal_bot, ← h]
        exact hp
      haveI : IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
        IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hne _
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p.asIdeal)
      have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
      have hmaxI := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
      haveI : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
        IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance
      haveI : Algebra.EssFiniteType k (Localization.AtPrime p.asIdeal) :=
        Algebra.EssFiniteType.comp k B _
      exact formallySmooth_of_maximalIdeal_eq_span_of_perfectField k _ ϖ hϖ0 hmaxI

    rw [← Algebra.smoothLocus_eq_univ_iff]
    apply Set.eq_univ_of_forall
    intro p
    obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
    let M : PrimeSpectrum B := ⟨m, hm.isPrime⟩
    have hM : M ∈ Algebra.smoothLocus k B := hmax M hm
    by_contra hp
    have hclosed : IsClosed (Algebra.smoothLocus k B)ᶜ := Algebra.isOpen_smoothLocus.isClosed_compl
    have hcl : M ∈ closure ({p} : Set (PrimeSpectrum B)) := (PrimeSpectrum.le_iff_mem_closure p
      M).mp hpm
    have hsub : closure ({p} : Set (PrimeSpectrum B)) ⊆ (Algebra.smoothLocus k B)ᶜ :=
      hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hp)
    exact hsub hcl hM
