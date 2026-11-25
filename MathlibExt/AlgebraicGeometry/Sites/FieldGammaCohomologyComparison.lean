/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado

module

public import MathlibExt.AlgebraicGeometry.Sites.FieldGlobalSectionsPullback
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleInverseImageExactness
public import MathlibExt.CategoryTheory.Abelian.RightDerived.DeltaComparison
public import MathlibExt.AlgebraicGeometry.Sites.FieldDerivedSectionsInvariants

/-!
# The original normalized global-section pullback and its fixed cohomology comparison
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- The existing actual Γ right-derived functors and their canonical connectors. -/
abbrev fieldOriginalGammaDeltaFunctor (k : Type u) [Field k] :
    CohomologicalDeltaFunctor
      (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      AddCommGrpCat.{max u w} :=
  Functor.rightDerivedDeltaFunctor
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})

theorem fieldOriginalGammaDeltaFunctor_isUniversal (k : Type u) [Field k] :
    CohomologicalDeltaFunctor.IsUniversal
      (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      AddCommGrpCat.{max u w} (fieldOriginalGammaDeltaFunctor.{u, w} k) :=
  Functor.isUniversal_rightDerivedDeltaFunctor
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})

variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]
attribute [local instance] IsSepClosure.sep_closed

/-- Register only the proved additivity of this SAME actual inverse image. -/
local instance fieldChangeInverseImage_additive (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).Additive :=
  smallEtaleInverseImage_additive.{u, w} (fieldOriginalPullback k Ω K Ψ e)


/-- Exactness of the actual inverse image supplies the real target delta functor. -/
def fieldInverseImageGammaDeltaFunctor (e : GaloisUnits.FieldMap k Ω K Ψ) :=
  CohomologicalDeltaFunctor.precompose
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
    (fun S hS => smallEtaleInverseImage_shortExact.{u, w}
      (fieldOriginalPullback k Ω K Ψ e) S hS)
    (fieldOriginalGammaDeltaFunctor.{u, w} K)

/-- Source universality extends the SAME actual adjunction-unit Γ map in every
degree; neither target injectivity nor a supplied comparison is required. -/
def fieldDerivedPullbackDeltaHom (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldOriginalGammaDeltaFunctor.{u, w} k ⟶
      fieldInverseImageGammaDeltaFunctor.{u, w} k Ω K Ψ e :=
  CohomologicalDeltaFunctor.normalizedExtension
    (fieldOriginalGammaDeltaFunctor.{u, w} k)
    (fieldInverseImageGammaDeltaFunctor.{u, w} k Ω K Ψ e)
    (fieldOriginalGammaDeltaFunctor_isUniversal.{u, w} k)
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf
    (Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
      (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf)
    (fieldPullbackGlobalSections.{u, w} k Ω K Ψ e)

/-- Every map uses the literal existing right-derived Γ objects. -/
def fieldDerivedPullback (e : GaloisUnits.FieldMap k Ω K Ψ) (n : ℕ) :
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived n ⟶
      smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
        (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived n :=
  CohomologicalDeltaFunctor.Hom.app (fieldDerivedPullbackDeltaHom.{u, w} k Ω K Ψ e) n

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
theorem fieldDerivedPullback_zero (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldDerivedPullback.{u, w} k Ω K Ψ e 0 ≫
        Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
          (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.hom =
      (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.hom ≫
        fieldPullbackGlobalSections.{u, w} k Ω K Ψ e :=
  CohomologicalDeltaFunctor.normalizedExtension_normalization
    (fieldOriginalGammaDeltaFunctor.{u, w} k)
    (fieldInverseImageGammaDeltaFunctor.{u, w} k Ω K Ψ e)
    (fieldOriginalGammaDeltaFunctor_isUniversal.{u, w} k)
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf
    (Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
      (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf)
    (fieldPullbackGlobalSections.{u, w} k Ω K Ψ e)

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
theorem fieldDerivedPullback_naturality (e : GaloisUnits.FieldMap k Ω K Ψ) (n : ℕ)
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q') :
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived n).map τ ≫
        (fieldDerivedPullback.{u, w} k Ω K Ψ e n).app Q' =
      (fieldDerivedPullback.{u, w} k Ω K Ψ e n).app Q ≫
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
          (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived n).map τ) :=
  (fieldDerivedPullback.{u, w} k Ω K Ψ e n).naturality τ


omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
/-- The independent same Γ map respects all canonical right-derived connectors. -/
theorem fieldDerivedPullback_connecting (e : GaloisUnits.FieldMap k Ω K Ψ) (n : ℕ)
    (S : ShortComplex.ShortExactSequences
      (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})) :
    ((fieldOriginalGammaDeltaFunctor.{u, w} k).connecting n).app S ≫
        (fieldDerivedPullback.{u, w} k Ω K Ψ e (n + 1)).app S.obj.X₁ =
      (fieldDerivedPullback.{u, w} k Ω K Ψ e n).app S.obj.X₃ ≫
        ((fieldInverseImageGammaDeltaFunctor.{u, w} k Ω K Ψ e).connecting n).app S :=
  DeltaFunctor.System.comm (fieldDerivedPullbackDeltaHom.{u, w} k Ω K Ψ e).hom n S

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
/-- Source universality fixes every degree of this actual map from its original zero map. -/
theorem fieldDerivedPullback_unique (e : GaloisUnits.FieldMap k Ω K Ψ)
    (g : fieldOriginalGammaDeltaFunctor.{u, w} k ⟶
      fieldInverseImageGammaDeltaFunctor.{u, w} k Ω K Ψ e)
    (hg : CohomologicalDeltaFunctor.Hom.app g 0 =
      fieldDerivedPullback.{u, w} k Ω K Ψ e 0) :
    g = fieldDerivedPullbackDeltaHom.{u, w} k Ω K Ψ e :=
  CohomologicalDeltaFunctor.hom_eq_of_app_zero
    (fieldOriginalGammaDeltaFunctor.{u, w} k)
    (fieldOriginalGammaDeltaFunctor_isUniversal.{u, w} k)
    (fieldInverseImageGammaDeltaFunctor.{u, w} k Ω K Ψ e) g
    (fieldDerivedPullbackDeltaHom.{u, w} k Ω K Ψ e) hg

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
/-- Each original coefficient morphism enters every actual ΓRD degree with ONE lift. -/
theorem fieldDerivedPullback_original_coefficient_naturality
    (e : GaloisUnits.FieldMap k Ω K Ψ) (n : ℕ)
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (τ : F ⟶ F') :
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived n).map
        ((liftCoefficients.{u, w} (Spec (.of k))).map τ) ≫
        (fieldDerivedPullback.{u, w} k Ω K Ψ e n).app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F') =
      (fieldDerivedPullback.{u, w} k Ω K Ψ e n).app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≫
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
          (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived n).map
            ((liftCoefficients.{u, w} (Spec (.of k))).map τ)) :=
  (fieldDerivedPullback.{u, w} k Ω K Ψ e n).naturality
    ((liftCoefficients.{u, w} (Spec (.of k))).map τ)

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The SAME accepted cut3 family, now packaged with its genuine connector squares. -/
def fieldGammaInvariantsDeltaIso :
    fieldOriginalGammaDeltaFunctor.{u, w} k ≅
      CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
        (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))
        (fieldDerivedInvariantsDeltaFunctor.{u, w} k Ω) :=
  Functor.RightDerived.precompDeltaIsoOfIso
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (fieldInvariantFunctor.{u, w} k Ω)
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω)

theorem fieldGammaInvariantsDeltaIso_hom_app (n : ℕ) :
    CohomologicalDeltaFunctor.Hom.app (fieldGammaInvariantsDeltaIso.{u, w} k Ω).hom n =
      (fieldDerivedSectionsInvariantsIso.{u, w} k Ω n).hom :=
  Functor.RightDerived.precompDeltaIsoOfIso_hom_app
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (fieldInvariantFunctor.{u, w} k Ω)
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) n

/-- The SAME accepted all-degree Γ/old-native-cohomology comparison is a delta isomorphism. -/
def fieldGammaContinuousDeltaIso :
    fieldOriginalGammaDeltaFunctor.{u, w} k ≅
      CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
        (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))
        (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω) :=
  fieldGammaInvariantsDeltaIso.{u, w} k Ω ≪≫
    (CohomologicalDeltaFunctor.precomposeFunctor (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
      (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))).mapIso
        (fieldContinuousDerivedInvariantsDeltaIso.{u, w} k Ω).symm

theorem fieldGammaContinuousDeltaIso_hom_app (n : ℕ) :
    CohomologicalDeltaFunctor.Hom.app (fieldGammaContinuousDeltaIso.{u, w} k Ω).hom n =
      (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω n).hom := rfl

end AlgebraicGeometry.Scheme.DerivedSections

end
