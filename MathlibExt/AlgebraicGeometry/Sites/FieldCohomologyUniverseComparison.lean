/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado

module

public import MathlibExt.RepresentationTheory.Homological.ContCohomology.UniverseComparison
public import MathlibExt.CategoryTheory.NatIso.ComparisonCoherence
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.PrecompositionCoherence
public import MathlibExt.AlgebraicGeometry.Sites.FieldContinuousCohomologyDerivedInvariants

/-!
# Rank coordinates for continuous field cohomology

The field coefficient category already uses carrier universe `max u w`. Reparameterizing the
auxiliary rank `w` as `max u w` gives a natural comparison of the continuous-cohomology
constructions, compatible with connecting maps and the degree-zero invariant coordinate.

A continuous homomorphism between the two Galois groups gives restriction on coefficients and
cohomology. Conjugating by these rank comparisons produces the restriction delta morphism at
the stated rank, whose components are the homology maps of the corresponding continuous
homogeneous-cochain restriction.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Rank reparameterization gives a continuous cohomology isomorphism.

The degree-`q` continuous-cohomology functors with parameters `w` and `max u w` are naturally
isomorphic on the common-rank coefficient category. -/
def fieldSameRankContinuousIso (q : ℕ) :
    fieldContinuousCohomologyFunctor.{u, w} k Ω q ≅
      fieldContinuousCohomologyFunctor.{u, max u w} k Ω q :=
  ContinuousCohomology.sameRankDiscreteCohomologyNatIso.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω) q

/-- Rank comparison commutes with coefficient connecting maps.

The two rank coordinates identify the connecting morphisms of every short exact coefficient
sequence. -/
theorem fieldSameRankContinuousIso_connecting (q : ℕ)
    (S : ShortComplex.ShortExactSequences (FieldCohomologyModule.{u, w} k Ω)) :
    ((fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω).connecting q).app S ≫
        (fieldSameRankContinuousIso.{u, w} k Ω (q + 1)).hom.app S.obj.X₁ =
      (fieldSameRankContinuousIso.{u, w} k Ω q).hom.app S.obj.X₃ ≫
        ((fieldContinuousCohomologyDeltaFunctor.{u, max u w} k Ω).connecting q).app S :=
  ContinuousCohomology.sameRank_discrete_connecting.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω) S.obj
    (fieldShortExact_discreteCoefficientExact.{u, w} k Ω S.obj S.property)
    (fieldShortExact_discreteCoefficientExact.{u, max u w} k Ω S.obj S.property) q

/-- Rank comparison is an isomorphism of delta functors.

The degreewise rank comparisons and connecting-map compatibility assemble to an isomorphism of
the continuous-cohomology delta functors. -/
def fieldSameRankContinuousDeltaIso :
    fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω ≅
      fieldContinuousCohomologyDeltaFunctor.{u, max u w} k Ω :=
  CohomologicalDeltaFunctor.isoOfComponents
    (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω)
    (fieldContinuousCohomologyDeltaFunctor.{u, max u w} k Ω)
    (fieldSameRankContinuousIso.{u, w} k Ω)
    (fieldSameRankContinuousIso_connecting.{u, w} k Ω)

/-- Degree component of the rank delta comparison.

Its degree-`q` morphism is the forward map of `fieldSameRankContinuousIso`. -/
@[simp] theorem fieldSameRankContinuousDeltaIso_hom_app (q : ℕ) :
    CohomologicalDeltaFunctor.Hom.app
      (fieldSameRankContinuousDeltaIso.{u, w} k Ω).hom q =
        (fieldSameRankContinuousIso.{u, w} k Ω q).hom := rfl

/-- Rank comparison preserves the invariant coordinate in degree zero.

The rank comparison followed by the enlarged-parameter zero-degree coordinate equals the
stated-rank zero-degree coordinate. -/
theorem fieldSameRankContinuousIso_zero :
    (fieldSameRankContinuousIso.{u, w} k Ω 0).hom ≫
        (fieldContinuousCohomologyZeroIso.{u, max u w} k Ω).hom =
      (fieldContinuousCohomologyZeroIso.{u, w} k Ω).hom := by
  apply NatTrans.ext
  funext M
  exact ContinuousCohomology.sameRank_discrete_zero.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω) M

variable (K Ψ : Type u) [Field K] [Field Ψ] [Algebra K Ψ] [IsSepClosure K Ψ]

-- Earlier V5 recorded the real original/wide cochain mismatch; the proved adapter now supplies it.
/-- Group restriction delta morphism in the stated field rank.

For a continuous Galois-group homomorphism, conjugate the restriction map by the source and
target rank comparisons to obtain a morphism of delta functors. -/
def fieldOriginalRankRestrictionDeltaHom
    (φ : InfiniteGalois.profiniteGalGrp K Ψ →ₜ* InfiniteGalois.profiniteGalGrp k Ω) :
    fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω ⟶
      CohomologicalDeltaFunctor.precompose
        (fieldModuleRestriction.{u, u, w} k Ω K Ψ φ)
        (fieldModuleRestriction_shortExact.{u, u, w} k Ω K Ψ φ)
        (fieldContinuousCohomologyDeltaFunctor.{u, w} K Ψ) := by
  let C := FieldCohomologyModule.{u, w} k Ω
  let B := FieldCohomologyModule.{u, w} K Ψ
  let D := AddCommGrpCat.{max u w}
  let R : C ⥤ B := fieldModuleRestriction.{u, u, w} k Ω K Ψ φ
  let _ : R.Additive := fieldModuleRestriction_additive.{u, u, w} k Ω K Ψ φ
  let hR : ∀ S : ShortComplex C, S.ShortExact → (S.map R).ShortExact :=
    fieldModuleRestriction_shortExact.{u, u, w} k Ω K Ψ φ
  let S : CohomologicalDeltaFunctor C D := fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω
  let S' : CohomologicalDeltaFunctor C D :=
    fieldContinuousCohomologyDeltaFunctor.{u, max u w} k Ω
  let T : CohomologicalDeltaFunctor B D := fieldContinuousCohomologyDeltaFunctor.{u, w} K Ψ
  let T' : CohomologicalDeltaFunctor B D :=
    fieldContinuousCohomologyDeltaFunctor.{u, max u w} K Ψ
  let eS : S ≅ S' := fieldSameRankContinuousDeltaIso.{u, w} k Ω
  let eT : T ≅ T' := fieldSameRankContinuousDeltaIso.{u, w} K Ψ
  let d : S' ⟶ CohomologicalDeltaFunctor.precompose R hR T' :=
    fieldContinuousRestrictionDeltaHom.{u, u, w} k Ω K Ψ φ
  let P : CohomologicalDeltaFunctor B D ⥤ CohomologicalDeltaFunctor C D :=
    CohomologicalDeltaFunctor.precomposeFunctor R hR
  exact eS.hom ≫ d ≫ P.map eT.inv

-- Typed components of the proved old/wide delta comparison.
/-- Degree map of the stated rank restriction.

The degree component is source rank comparison, continuous cohomology restriction, and inverse
target rank comparison whiskered by coefficient restriction. -/
theorem fieldOriginalRankRestrictionDeltaHom_app
    (φ : InfiniteGalois.profiniteGalGrp K Ψ →ₜ* InfiniteGalois.profiniteGalGrp k Ω) (q : ℕ) :
    CohomologicalDeltaFunctor.Hom.app
      (fieldOriginalRankRestrictionDeltaHom.{u, w} k Ω K Ψ φ) q =
    (fieldSameRankContinuousIso.{u, w} k Ω q).hom ≫
      fieldContinuousCohomologyRestriction.{u, u, w} k Ω K Ψ q φ ≫
      Functor.whiskerLeft (fieldModuleRestriction.{u, u, w} k Ω K Ψ φ)
        (fieldSameRankContinuousIso.{u, w} K Ψ q).inv := by
  let C := FieldCohomologyModule.{u, w} k Ω
  let B := FieldCohomologyModule.{u, w} K Ψ
  let D := AddCommGrpCat.{max u w}
  let R : C ⥤ B := fieldModuleRestriction.{u, u, w} k Ω K Ψ φ
  let _ : R.Additive := fieldModuleRestriction_additive.{u, u, w} k Ω K Ψ φ
  let hR : ∀ S : ShortComplex C, S.ShortExact → (S.map R).ShortExact :=
    fieldModuleRestriction_shortExact.{u, u, w} k Ω K Ψ φ
  let S : CohomologicalDeltaFunctor C D := fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω
  let S' : CohomologicalDeltaFunctor C D :=
    fieldContinuousCohomologyDeltaFunctor.{u, max u w} k Ω
  let T : CohomologicalDeltaFunctor B D := fieldContinuousCohomologyDeltaFunctor.{u, w} K Ψ
  let T' : CohomologicalDeltaFunctor B D :=
    fieldContinuousCohomologyDeltaFunctor.{u, max u w} K Ψ
  let eS : S ≅ S' := fieldSameRankContinuousDeltaIso.{u, w} k Ω
  let eT : T ≅ T' := fieldSameRankContinuousDeltaIso.{u, w} K Ψ
  let d : S' ⟶ CohomologicalDeltaFunctor.precompose R hR T' :=
    fieldContinuousRestrictionDeltaHom.{u, u, w} k Ω K Ψ φ
  let P : CohomologicalDeltaFunctor B D ⥤ CohomologicalDeltaFunctor C D :=
    CohomologicalDeltaFunctor.precomposeFunctor R hR
  have hSource : CohomologicalDeltaFunctor.Hom.app eS.hom q =
      (fieldSameRankContinuousIso.{u, w} k Ω q).hom :=
    fieldSameRankContinuousDeltaIso_hom_app.{u, w} k Ω q
  have hRestriction : CohomologicalDeltaFunctor.Hom.app d q =
      fieldContinuousCohomologyRestriction.{u, u, w} k Ω K Ψ q φ := rfl
  have hPrecompose : CohomologicalDeltaFunctor.Hom.app (P.map eT.inv) q =
      Functor.whiskerLeft R (CohomologicalDeltaFunctor.Hom.app eT.inv q) :=
    CohomologicalDeltaFunctor.delta_precompose_map_app R hR eT.inv q
  have hInverse : CohomologicalDeltaFunctor.Hom.app eT.inv q =
      (fieldSameRankContinuousIso.{u, w} K Ψ q).inv := rfl
  change CohomologicalDeltaFunctor.Hom.app eS.hom q ≫
      CohomologicalDeltaFunctor.Hom.app d q ≫
        CohomologicalDeltaFunctor.Hom.app (P.map eT.inv) q = _
  rw [hSource, hRestriction, hPrecompose, hInverse]

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

/-- Continuous cochain restriction in the stated rank.

The group homomorphism and canonical coefficient intertwiner give the homogeneous-cochain
restriction map in the given rank coordinates. -/
def fieldOriginalRankRestrictionCochainMap
    (φ : InfiniteGalois.profiniteGalGrp K Ψ →ₜ* InfiniteGalois.profiniteGalGrp k Ω)
    (M : FieldCohomologyModule.{u, w} k Ω) :=
  ContinuousCohomology.sameRankOriginalGroupCochainMap.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω) (InfiniteGalois.profiniteGalGrp K Ψ) φ
    (fieldModuleRestrictionTopRepHom.{u, u, w} k Ω K Ψ φ M)

-- V5 retained the actual old/wide model mismatch; the full proved cochain square resolves it.
/-- Rank restriction degree map is the cochain homology map.

At a coefficient module, the delta restriction component equals the underlying additive map
induced on homology by the stated-rank homogeneous-cochain map. -/
theorem fieldOriginalRankRestrictionDeltaHom_original_map
    (φ : InfiniteGalois.profiniteGalGrp K Ψ →ₜ* InfiniteGalois.profiniteGalGrp k Ω)
    (q : ℕ) (M : FieldCohomologyModule.{u, w} k Ω) :
    (CohomologicalDeltaFunctor.Hom.app
      (fieldOriginalRankRestrictionDeltaHom.{u, w} k Ω K Ψ φ) q).app M =
    ContinuousCohomology.discreteCoefficientForget.{max u w}.map
      (HomologicalComplex.homologyMap
        (fieldOriginalRankRestrictionCochainMap.{u, w} k Ω K Ψ φ M) q) := by
  let G := InfiniteGalois.profiniteGalGrp k Ω
  let H := InfiniteGalois.profiniteGalGrp K Ψ
  let R := fieldModuleRestriction.{u, u, w} k Ω K Ψ φ
  let X : TopRep.{max u w, 0, u} ℤ G :=
    (ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w} G).obj M
  let Y : TopRep.{max u w, 0, u} ℤ H :=
    (ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w} H).obj (R.obj M)
  let f : TopRep.res φ X ⟶ Y :=
    fieldModuleRestrictionTopRepHom.{u, u, w} k Ω K Ψ φ M
  let F : TopModuleCat.{max u w} ℤ ⥤ AddCommGrpCat.{max u w} :=
    ContinuousCohomology.discreteCoefficientForget.{max u w}
  let eS : (fieldContinuousCohomologyFunctor.{u, w} k Ω q).obj M ≅
      (fieldContinuousCohomologyFunctor.{u, max u w} k Ω q).obj M :=
    (fieldSameRankContinuousIso.{u, w} k Ω q).app M
  let eT : (fieldContinuousCohomologyFunctor.{u, w} K Ψ q).obj (R.obj M) ≅
      (fieldContinuousCohomologyFunctor.{u, max u w} K Ψ q).obj (R.obj M) :=
    (fieldSameRankContinuousIso.{u, w} K Ψ q).app (R.obj M)
  let a : (fieldContinuousCohomologyFunctor.{u, w} k Ω q).obj M ⟶
      (fieldContinuousCohomologyFunctor.{u, w} K Ψ q).obj (R.obj M) :=
    F.map (HomologicalComplex.homologyMap
      (ContinuousCohomology.sameRankOriginalGroupCochainMap.{u, w} G H φ f) q)
  let b : (fieldContinuousCohomologyFunctor.{u, max u w} k Ω q).obj M ⟶
      (fieldContinuousCohomologyFunctor.{u, max u w} K Ψ q).obj (R.obj M) :=
    F.map (ContinuousCohomology.nativeGroupCoefficientCohomologyMap.{0, u, u, w} φ f q)
  have hm : ContinuousCohomology.sameRankOriginalGroupCochainMap.{u, max u w} G H φ f =
      ContinuousCohomology.nativeGroupCoefficientCochainsMap.{0, u, u, w} φ f :=
    (ContinuousCohomology.nativeGroupCoefficientCochainsMap_eq_stock φ f).symm
  have hSquare : a ≫ eT.hom = eS.hom ≫ b := by
    have h := ContinuousCohomology.sameRank_original_group_cohomology_square.{u, w} G H φ f q
    rw [hm] at h
    have hh := congrArg F.map h
    simpa only [Functor.map_comp] using hh
  change eS.hom ≫ b ≫ eT.inv = a
  exact rankIso_transport_map_eq eS eT a b hSquare

end AlgebraicGeometry.Scheme.DerivedSections

end
