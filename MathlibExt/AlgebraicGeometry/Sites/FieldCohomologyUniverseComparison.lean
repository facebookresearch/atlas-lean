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
# The same original field cochains, connecting maps and group restriction at the original coefficient rank
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

/-- Actual original-cochain isomorphism on the same common field module in every degree. -/
def fieldSameRankContinuousIso (q : ℕ) :
    fieldContinuousCohomologyFunctor.{u, w} k Ω q ≅
      fieldContinuousCohomologyFunctor.{u, max u w} k Ω q :=
  ContinuousCohomology.sameRankDiscreteCohomologyNatIso.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω) q

/-- Actual source and target field connectors commute with the fixed original cochain comparison. -/
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

/-- One genuine delta isomorphism, with the SAME original model and no second coefficient lift. -/
def fieldSameRankContinuousDeltaIso :
    fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω ≅
      fieldContinuousCohomologyDeltaFunctor.{u, max u w} k Ω :=
  CohomologicalDeltaFunctor.isoOfComponents
    (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω)
    (fieldContinuousCohomologyDeltaFunctor.{u, max u w} k Ω)
    (fieldSameRankContinuousIso.{u, w} k Ω)
    (fieldSameRankContinuousIso_connecting.{u, w} k Ω)

@[simp] theorem fieldSameRankContinuousDeltaIso_hom_app (q : ℕ) :
    CohomologicalDeltaFunctor.Hom.app
      (fieldSameRankContinuousDeltaIso.{u, w} k Ω).hom q =
        (fieldSameRankContinuousIso.{u, w} k Ω q).hom := rfl

/-- The SAME old identity evaluation normalizes the original-rank comparison. -/
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
/-- The actual group restriction, transported between the SAME old original cochain models. -/
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

/-- The SAME old original nested cochain map for the actual neutral field restriction. -/
def fieldOriginalRankRestrictionCochainMap
    (φ : InfiniteGalois.profiniteGalGrp K Ψ →ₜ* InfiniteGalois.profiniteGalGrp k Ω)
    (M : FieldCohomologyModule.{u, w} k Ω) :=
  ContinuousCohomology.sameRankOriginalGroupCochainMap.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω) (InfiniteGalois.profiniteGalGrp K Ψ) φ
    (fieldModuleRestrictionTopRepHom.{u, u, w} k Ω K Ψ φ M)

-- V5 retained the actual old/wide model mismatch; the full proved cochain square resolves it.
/-- The transported delta map in EVERY degree is the literal old original cochain homology map. -/
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
