/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_CurveModelSmooth.lean`
and
`P2M/Sol/S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
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

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.Curve.ChartRing
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Smoothness of chart rings

Over a perfect field `K`, if `s ∈ L` is transcendental over `K` and `L` is finite and separable
over `K(s)`, then `Spec` of the chart ring of `{s}` is smooth of relative dimension one over
`Spec K` (`AlgebraicCurve.CurveModel.smoothOfRelativeDimension_one_Spec_chartRing`).
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial Algebra IntermediateField IsLocalRing
open scoped IntermediateField.algebraAdjoinAdjoin

universe u

namespace AlgebraicCurve.CurveModel

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L]

section Coordinate

variable {A : Type u} [CommRing A] [Algebra K A]

private theorem exists_mem_and_maximalIdeal_eq_span [IsDedekindDomain A] (𝔪 : Ideal A)
    [𝔪.IsPrime] (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ u : A, u ∈ 𝔪 ∧ u ≠ 0 ∧
      maximalIdeal (Localization.AtPrime 𝔪) =
        Ideal.span {algebraMap A (Localization.AtPrime 𝔪) u} := by
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A h𝔪
    (Localization.AtPrime 𝔪)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime 𝔪)
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj 𝔪.primeCompl ϖ
  have hbu : IsUnit (algebraMap A (Localization.AtPrime 𝔪) (b : A)) :=
    IsLocalization.map_units _ b
  have hirr : Irreducible (algebraMap A (Localization.AtPrime 𝔪) a) := by
    rw [← hab]
    exact (irreducible_mul_isUnit hbu).mpr hϖ
  refine ⟨a, ?_, ?_, (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirr⟩
  · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 a).mp
      ((mem_maximalIdeal _).mpr hirr.not_isUnit)
  · rintro rfl
    exact hirr.ne_zero (map_zero _)

private theorem transcendental_of_mem [IsDomain A] {𝔪 : Ideal A} (hne : 𝔪 ≠ ⊤) {u : A}
    (hu : u ∈ 𝔪) (h0 : u ≠ 0) : Transcendental K u := by
  intro halg
  have hint : IsIntegral K u := halg.isIntegral
  have hc : (minpoly K u).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint h0
  have h := minpoly.aeval K u
  rw [← (minpoly K u).X_mul_divX_add, map_add, map_mul, Polynomial.aeval_X,
    Polynomial.aeval_C] at h
  have key : algebraMap K A ((minpoly K u).coeff 0) =
      -(u * Polynomial.aeval u (minpoly K u).divX) :=
    eq_neg_of_add_eq_zero_right h
  exact hne (𝔪.eq_top_of_isUnit_mem (key ▸ 𝔪.neg_mem (𝔪.mul_mem_right _ hu))
    ((IsUnit.mk0 _ hc).map _))

end Coordinate

private instance isStandardSmoothOfRelativeDimension_polynomial (R : Type u) [CommRing R] :
    IsStandardSmoothOfRelativeDimension 1 R R[X] :=
  IsStandardSmoothOfRelativeDimension.of_algEquiv 1 (MvPolynomial.uniqueAlgEquiv R (Fin 1))

private theorem isStandardSmoothOfRelativeDimension_adjoin_single (s : L)
    (hs : Transcendental K s) :
    IsStandardSmoothOfRelativeDimension 1 K (Algebra.adjoin K {s}) := by
  have e : K[X] ≃ₐ[K] Algebra.adjoin K ({s} : Set L) :=
    (AlgEquiv.ofInjective (Polynomial.aeval (R := K) s)
      (transcendental_iff_injective.mp hs)).trans
      (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval K s).symm)
  exact IsStandardSmoothOfRelativeDimension.of_algEquiv 1 e

private theorem rank_kaehler_eq_of_formallyEtale (B C : Type u) [CommRing B] [CommRing C]
    [Algebra K B] [Algebra K C] [Algebra B C] [IsScalarTower K B C]
    (M : Submonoid B) (hM : M ≤ nonZeroDivisors B) [IsLocalization M C] :
    Module.rank B Ω[B⁄K] = Module.rank C Ω[C⁄K] := by
  have : FormallyEtale B C := FormallyEtale.of_isLocalization (Rₘ := C) M
  have : IsLocalizedModule M ((KaehlerDifferential.map K K B C).restrictScalars B) :=
    (isLocalizedModule_iff_isBaseChange M C _).mpr
      (KaehlerDifferential.isBaseChange_of_formallyEtale K B C)
  rw [← IsLocalizedModule.rank_eq M hM ((KaehlerDifferential.map K K B C).restrictScalars B)]
  exact (IsLocalization.rank_eq C M hM).symm

private theorem rank_kaehler_intermediateField_adjoin_single (s : L)
    (hs : Transcendental K s) : Module.rank K⟮s⟯ Ω[K⟮s⟯⁄K] = 1 := by
  have := isStandardSmoothOfRelativeDimension_adjoin_single K s hs
  have h1 : Module.rank (Algebra.adjoin K ({s} : Set L)) Ω[(Algebra.adjoin K ({s} : Set L))⁄K]
      = 1 := IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 1
  rw [← rank_kaehler_eq_of_formallyEtale K (Algebra.adjoin K ({s} : Set L)) (↥K⟮s⟯)
    (nonZeroDivisors _) le_rfl]
  exact_mod_cast h1

section OneGenerator

variable (s : L) [FiniteDimensional K⟮s⟯ L] [Algebra.IsSeparable K⟮s⟯ L]

instance chartRing_finitePresentation : FinitePresentation K (chartRing K ({s} : Set L)) :=
  (Algebra.FinitePresentation.of_finiteType (R := K)).mp inferInstance

attribute [local instance] Ideal.Quotient.field

private theorem formallySmooth_chartRing_localization_closed [PerfectField K]
    (𝔪 : Ideal (chartRing K ({s} : Set L))) [𝔪.IsPrime] (h𝔪 : 𝔪 ≠ ⊥) :
    FormallySmooth K (Localization.AtPrime 𝔪) := by
  have h𝔪max : 𝔪.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h𝔪
  obtain ⟨u, hu𝔪, hu0, hspan⟩ := exists_mem_and_maximalIdeal_eq_span 𝔪 h𝔪
  have hu : Transcendental K u := transcendental_of_mem K h𝔪max.ne_top hu𝔪 hu0
  let alg : Algebra K[X] (chartRing K ({s} : Set L)) :=
    (Polynomial.aeval u : K[X] →ₐ[K] chartRing K ({s} : Set L)).toRingHom.toAlgebra
  have halg : ∀ f : K[X],
      algebraMap K[X] (chartRing K ({s} : Set L)) f = Polynomial.aeval u f :=
    fun _ => rfl
  have : IsScalarTower K K[X] (chartRing K ({s} : Set L)) :=
    IsScalarTower.of_algebraMap_eq fun k => ((Polynomial.aeval u).commutes k).symm
  have : IsScalarTower K K[X] (Localization.AtPrime 𝔪) :=
    IsScalarTower.of_algebraMap_eq fun k => by
      rw [IsScalarTower.algebraMap_apply K (chartRing K ({s} : Set L)) (Localization.AtPrime 𝔪),
        IsScalarTower.algebraMap_apply K[X] (chartRing K ({s} : Set L))
          (Localization.AtPrime 𝔪),
        IsScalarTower.algebraMap_apply K K[X] (chartRing K ({s} : Set L))]
  have : Module.IsTorsionFree K[X] (chartRing K ({s} : Set L)) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (transcendental_iff_injective.mp hu)
  have : Module.Flat K[X] (chartRing K ({s} : Set L)) := inferInstance
  have : Algebra.FiniteType K[X] (chartRing K ({s} : Set L)) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K K[X] (chartRing K ({s} : Set L))
  have : Algebra.FinitePresentation K[X] (chartRing K ({s} : Set L)) :=
    (Algebra.FinitePresentation.of_finiteType).mp ‹_›
  have hXp : (X : K[X]) ∈ 𝔪.under K[X] := by
    change algebraMap K[X] (chartRing K ({s} : Set L)) X ∈ 𝔪
    rwa [halg, Polynomial.aeval_X]
  have : (𝔪.under K[X]).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance fun h =>
      Polynomial.X_ne_zero ((Submodule.eq_bot_iff _).mp h X hXp)
  let := Localization.AtPrime.algebraOfLiesOver (𝔪.under K[X]) 𝔪
  have : Module.Finite K (K[X] ⧸ 𝔪.under K[X]) :=
    finite_of_finite_type_of_isJacobsonRing K _
  have : Algebra.IsAlgebraic K (K[X] ⧸ 𝔪.under K[X]) := Algebra.IsAlgebraic.of_finite K _
  have : PerfectField (K[X] ⧸ 𝔪.under K[X]) := Algebra.IsAlgebraic.perfectField (K := K)
  have : Module.Finite K (chartRing K ({s} : Set L) ⧸ 𝔪) :=
    finite_of_finite_type_of_isJacobsonRing K _
  have : Module.Finite (K[X] ⧸ 𝔪.under K[X]) (chartRing K ({s} : Set L) ⧸ 𝔪) :=
    Module.Finite.of_restrictScalars_finite K _ _
  have : Algebra.IsAlgebraic (K[X] ⧸ 𝔪.under K[X]) (chartRing K ({s} : Set L) ⧸ 𝔪) :=
    Algebra.IsAlgebraic.of_finite _ _
  have : Algebra.IsSeparable (K[X] ⧸ 𝔪.under K[X]) (chartRing K ({s} : Set L) ⧸ 𝔪) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Algebra.IsUnramifiedAt K[X] 𝔪 := by
    rw [Algebra.isUnramifiedAt_iff_map_eq (p := 𝔪.under K[X])]
    refine ⟨inferInstance, le_antisymm ?_ ?_⟩
    · refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
      rw [Ideal.mem_comap,
        IsScalarTower.algebraMap_apply K[X] (chartRing K ({s} : Set L)) (Localization.AtPrime 𝔪)]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 _).mpr hf
    · rw [hspan, Ideal.span_le, Set.singleton_subset_iff]
      have : algebraMap (chartRing K ({s} : Set L)) (Localization.AtPrime 𝔪) u =
          algebraMap K[X] (Localization.AtPrime 𝔪) X := by
        rw [IsScalarTower.algebraMap_apply K[X] (chartRing K ({s} : Set L))
          (Localization.AtPrime 𝔪), halg, Polynomial.aeval_X]
      rw [SetLike.mem_coe, this]
      exact Ideal.mem_map_of_mem _ hXp
  have : Algebra.IsEtaleAt K[X] 𝔪 := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat 𝔪
  have : Algebra.FormallySmooth K[X] (Localization.AtPrime 𝔪) := inferInstance
  exact Algebra.FormallySmooth.comp K K[X] (Localization.AtPrime 𝔪)

private theorem formallySmooth_chartRing_localization_bot [PerfectField K] :
    FormallySmooth K (Localization.AtPrime (⊥ : Ideal (chartRing K ({s} : Set L)))) := by
  let A := chartRing K ({s} : Set L)
  have heq : (⊥ : Ideal A).primeCompl = nonZeroDivisors A := by
    ext x; simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
  have : IsLocalization (⊥ : Ideal A).primeCompl L :=
    heq.symm ▸ (inferInstance : IsFractionRing A L)
  let e : L ≃ₐ[K] Localization.AtPrime (⊥ : Ideal A) :=
    (IsLocalization.algEquiv (⊥ : Ideal A).primeCompl L _).restrictScalars K
  have : EssFiniteType (↥A) L :=
    EssFiniteType.of_isLocalization (S := L) (nonZeroDivisors (A : Type u))
  have : EssFiniteType K L := EssFiniteType.comp K (↥A) L
  exact FormallySmooth.of_equiv e

private theorem chartRing_isSmoothAt [PerfectField K] (𝔭 : Ideal (chartRing K ({s} : Set L)))
    [𝔭.IsPrime] : IsSmoothAt K 𝔭 := by
  rcases eq_or_ne 𝔭 ⊥ with rfl | h𝔭
  · exact formallySmooth_chartRing_localization_bot K s
  · exact formallySmooth_chartRing_localization_closed K s 𝔭 h𝔭

omit [FiniteDimensional K⟮s⟯ L] in
/-- If `L` is separable algebraic over `K(s)` with `s` transcendental, then `Ω[L⁄K]` has rank
one over `L`. -/
theorem rank_kaehler_eq_one_of_isSeparable (hs : Transcendental K s) :
    Module.rank L Ω[L⁄K] = 1 := by
  have : FormallyEtale (↥K⟮s⟯) L := FormallyEtale.of_isSeparable (↥K⟮s⟯) L
  have e := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (↥K⟮s⟯) L).symm
  rw [e.rank_eq, Module.rank_baseChange, rank_kaehler_intermediateField_adjoin_single K s hs]
  simp

private theorem rank_kaehler_chartRing_localization_away_eq_one (hs : Transcendental K s)
    (t : chartRing K ({s} : Set L)) (ht : t ≠ 0) :
    Module.rank (Localization.Away t) Ω[(Localization.Away t)⁄K] = 1 := by
  have htnzd := powers_le_nonZeroDivisors_of_noZeroDivisors ht
  have : IsDomain (Localization.Away t) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away t) htnzd
  let : Algebra (Localization.Away t) L :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.Away t) L
      (Submonoid.powers t) (nonZeroDivisors _) htnzd
  have : IsScalarTower (chartRing K ({s} : Set L)) (Localization.Away t) L :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.Away t) L
      (Submonoid.powers t) (nonZeroDivisors _) htnzd
  have : IsScalarTower K (Localization.Away t) L :=
    IsScalarTower.of_algebraMap_eq (S := Localization.Away t) (A := L) fun a => by
      rw [IsScalarTower.algebraMap_apply K (↥(chartRing K ({s} : Set L)))
          (Localization.Away t) a,
        ← IsScalarTower.algebraMap_apply (↥(chartRing K ({s} : Set L))) (Localization.Away t) L,
        ← IsScalarTower.algebraMap_apply K (↥(chartRing K ({s} : Set L))) L]
  have : IsFractionRing (Localization.Away t) L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers t) (Localization.Away t) L
  rw [rank_kaehler_eq_of_formallyEtale K (Localization.Away t) L (nonZeroDivisors _) le_rfl]
  exact_mod_cast rank_kaehler_eq_one_of_isSeparable K s hs

/-- Over a perfect field `K`, the chart ring of `{s}` is formally smooth over `K` when `L` is
finite and separable over `K(s)`. -/
theorem formallySmooth_chartRing [PerfectField K] :
    FormallySmooth K (chartRing K ({s} : Set L)) := by
  rw [← smoothLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  exact fun 𝔭 => chartRing_isSmoothAt K s 𝔭.asIdeal

private theorem locally_isStandardSmoothOfRelativeDimension_one_chartRing [PerfectField K]
    (hs : Transcendental K s) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap K (chartRing K ({s} : Set L))) := by
  have : Algebra.Smooth K (chartRing K ({s} : Set L)) :=
    { formallySmooth := formallySmooth_chartRing K s
      finitePresentation := chartRing_finitePresentation K s }
  obtain ⟨σ, hσ, hstd⟩ :=
    Algebra.Smooth.exists_span_eq_top_isStandardSmooth K (chartRing K ({s} : Set L))
  refine ⟨σ \ {0}, by rw [Ideal.span_sdiff_singleton_zero]; exact hσ, fun t ht => ?_⟩
  obtain ⟨htσ, ht0⟩ := ht; simp only [Set.mem_singleton_iff] at ht0
  change RingHom.IsStandardSmoothOfRelativeDimension 1
    ((algebraMap _ (Localization.Away t)).comp (algebraMap K (chartRing K ({s} : Set L))))
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  have := hstd t htσ
  have : IsDomain (Localization.Away t) := IsLocalization.isDomain_of_le_nonZeroDivisors
    (Localization.Away t) (powers_le_nonZeroDivisors_of_noZeroDivisors ht0)
  exact (IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth 1).mpr
    (rank_kaehler_chartRing_localization_away_eq_one K s hs t ht0)

/-- Over a perfect field, `Spec` of the chart ring of a transcendental `s`, with `L` finite
separable over `K(s)`, is smooth of relative dimension one over `Spec K`. -/
theorem smoothOfRelativeDimension_one_Spec_chartRing [PerfectField K]
    (hs : Transcendental K s) :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({s} : Set L))))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact locally_isStandardSmoothOfRelativeDimension_one_chartRing K s hs

end OneGenerator

end AlgebraicCurve.CurveModel
