/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Abelian.RightDerived.Precomposition
public import MathlibExt.AlgebraicGeometry.Sites.FieldGlobalSectionsInvariants

/-! # Actual derived Gamma and invariants under the fixed field equivalence -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

-- Check the native comparison equations over abstract categories before
-- substituting the sheaf and Galois-action functors.
section DerivedComparisonProofs

universe uC vC uD vD uA vA

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [HasInjectiveResolutions D]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (T : C ⥤ D) [T.Additive] [T.PreservesInjectiveObjects] [T.PreservesHomology]
variable (G : D ⥤ A) [G.Additive]
variable {P : C ⥤ A} [P.Additive]

private theorem derivedResolutionFormulaProof (α : P ≅ T ⋙ G) (q : ℕ)
    {Q : C} (I : InjectiveResolution Q) :
    (Functor.rightDerivedPrecompIsoOfIso T G α q).hom.app Q =
      (I.isoRightDerivedObj P q).hom ≫
        (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q).map
          ((NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app I.cocomplex) ≫
        (Functor.rightDerivedPrecompHomologyIso T G q I).hom ≫
        ((T.mapInjectiveResolution I).isoRightDerivedObj G q).inv :=
  Functor.rightDerivedPrecompIsoOfIso_resolution_formula T G α q I

private theorem derivedZeroMapProof (α : P ≅ T ⋙ G) (Q : C) :
    P.toRightDerivedZero.app Q ≫
        (Functor.rightDerivedPrecompIsoOfIso T G α 0).hom.app Q =
      α.hom.app Q ≫ G.toRightDerivedZero.app (T.obj Q) :=
  Functor.rightDerivedPrecompIsoOfIso_toRightDerivedZero T G α Q

private theorem derivedZeroIsoProof
    [PreservesFiniteLimits P] [PreservesFiniteLimits G]
    (α : P ≅ T ⋙ G) (Q : C) :
    (Functor.rightDerivedPrecompIsoOfIso T G α 0).hom.app Q ≫
        G.rightDerivedZeroIsoSelf.hom.app (T.obj Q) =
      P.rightDerivedZeroIsoSelf.hom.app Q ≫ α.hom.app Q :=
  Functor.rightDerivedPrecompIsoOfIso_zeroIsoSelf T G α Q

private theorem derivedResolutionNaturalityProof (α : P ≅ T ⋙ G) (q : ℕ)
    {Q Q' : C} {f : Q ⟶ Q'} {I : InjectiveResolution Q}
    {J : InjectiveResolution Q'} (φ : InjectiveResolution.Hom I J f) :
    (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q).map
        ((P.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) ≫
      (Functor.rightDerivedPrecompHomologyIsoOfIso T G α q J).hom =
    (Functor.rightDerivedPrecompHomologyIsoOfIso T G α q I).hom ≫
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q).map
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (T.mapInjectiveResolutionHom φ).hom) :=
  Functor.rightDerivedPrecompHomologyIsoOfIso_naturality T G α q φ

private theorem derivedResolutionChoiceProof (α : P ≅ T ⋙ G) (q : ℕ)
    {Q : C} (I J : InjectiveResolution Q) :
    (InjectiveResolution.cohomologyComparisonIso I J P q).hom ≫
        (Functor.rightDerivedPrecompHomologyIsoOfIso T G α q J).hom =
      (Functor.rightDerivedPrecompHomologyIsoOfIso T G α q I).hom ≫
        (InjectiveResolution.cohomologyComparisonIso
          (T.mapInjectiveResolution I) (T.mapInjectiveResolution J) G q).hom :=
  Functor.rightDerivedPrecompHomologyIsoOfIso_comparison T G α q I J

private theorem derivedResolutionIsoProof (α : P ≅ T ⋙ G) (q : ℕ)
    {Q : C} (I : InjectiveResolution Q) :
    (Functor.rightDerivedPrecompIsoOfIso T G α q).hom.app Q =
      (I.isoRightDerivedObj P q).hom ≫
        (Functor.rightDerivedPrecompHomologyIsoOfIso T G α q I).hom ≫
        ((T.mapInjectiveResolution I).isoRightDerivedObj G q).inv :=
  Functor.rightDerivedPrecompIsoOfIso_resolution_iso T G α q I

end DerivedComparisonProofs

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The functor of `Gal(Ω/k)`-invariants, from discrete `Gal(Ω/k)`-modules to abelian groups. -/
abbrev fieldInvariantFunctor : FieldCohomologyModule.{u, w} k Ω ⥤ AddCommGrpCat.{max u w} :=
  DiscreteAbelianAction.invariantsFunctor

instance fieldInvariantFunctor_additive : (fieldInvariantFunctor.{u, w} k Ω).Additive where
  map_add {_ _} f g := by
    ext m
    apply Subtype.ext
    rfl

/-- The SAME original inverse, Gamma and equivalence counit give invariant left exactness. -/
def fieldInverseGammaInvariantsIso :
    fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω ⋙
      Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} ≅
      fieldInvariantFunctor.{u, w} k Ω :=
  Functor.isoWhiskerLeft (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω)
      (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) ≪≫
    (Functor.associator (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω)
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (fieldInvariantFunctor.{u, w} k Ω)).symm ≪≫
    Functor.isoWhiskerRight (fieldSheafGaloisEquivalence.{u, w} k Ω).counitIso
      (fieldInvariantFunctor.{u, w} k Ω) ≪≫ Functor.leftUnitor (fieldInvariantFunctor.{u, w} k Ω)

instance fieldInvariantFunctor_isRightAdjoint :
    (fieldInvariantFunctor.{u, w} k Ω).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (fieldInverseGammaInvariantsIso.{u, w} k Ω)

instance fieldInvariantFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (fieldInvariantFunctor.{u, w} k Ω) := by infer_instance

/-- The actual mapped injective resolution retains its actual augmentation and quasi-isomorphism. -/
abbrev fieldMappedInjectiveResolution
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    InjectiveResolution ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) :=
  (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapInjectiveResolution I

/-- The SAME cut2 comparison and actual precomposition give the full all-degree field family. -/
def fieldDerivedSectionsInvariantsIso (q : ℕ) :
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q ≅
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        (fieldInvariantFunctor.{u, w} k Ω).rightDerived q :=
  Functor.rightDerivedPrecompIsoOfIso (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    (fieldInvariantFunctor.{u, w} k Ω) (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) q

/-- Every actual source map has the SAME derived Gamma and mapped-invariant arrows. -/
theorem fieldDerivedSectionsInvariantsIso_naturality (q : ℕ)
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : Q ⟶ Q') :
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q).map f ≫
      (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).hom.app Q' =
    (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).hom.app Q ≫
      ((fieldInvariantFunctor.{u, w} k Ω).rightDerived q).map
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map f) :=
  (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).hom.naturality f


/-- The comparison keeps the actual homology of the SAME termwise cut2 map on ANY resolution. -/
theorem fieldDerivedSectionsInvariantsIso_resolution_formula (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    let C := Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}
    let D := FieldCohomologyModule.{u, w} k Ω
    let A := AddCommGrpCat.{max u w}
    let T : C ⥤ D := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    let G : D ⥤ A := fieldInvariantFunctor.{u, w} k Ω
    let P : C ⥤ A := Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}
    let _ : T.Additive := inferInstance
    let _ : T.PreservesInjectiveObjects := inferInstance
    let _ : T.PreservesHomology := inferInstance
    let _ : P.Additive := inferInstance
    let _ : G.Additive := fieldInvariantFunctor_additive.{u, w} k Ω
    let α : P ≅ T ⋙ G := fieldGlobalSectionsInvariantsIso.{u, w} k Ω
    let H : CochainComplex A ℕ ⥤ A :=
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q
    let I' : InjectiveResolution (T.obj Q) :=
      T.mapInjectiveResolution I
    let K₀ : CochainComplex A ℕ := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let K₁ : CochainComplex A ℕ :=
      ((T ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let K₂ : CochainComplex A ℕ := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I'.cocomplex
    let e : P.rightDerived q ≅ T ⋙ G.rightDerived q :=
      Functor.rightDerivedPrecompIsoOfIso T G α q
    let a : (P.rightDerived q).obj Q ≅ H.obj K₀ := I.isoRightDerivedObj P q
    let b : H.obj K₁ ≅ H.obj K₂ := Functor.rightDerivedPrecompHomologyIso T G q I
    let c : (G.rightDerived q).obj (T.obj Q) ≅ H.obj K₂ := I'.isoRightDerivedObj G q
    let τ : K₀ ⟶ K₁ :=
      (NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app I.cocomplex
    (e.hom.app Q : (P.rightDerived q).obj Q ⟶ (G.rightDerived q).obj (T.obj Q)) =
      (a.hom ≫ H.map τ ≫ b.hom ≫ c.inv :
        (P.rightDerived q).obj Q ⟶ (G.rightDerived q).obj (T.obj Q)) := by
  exact derivedResolutionFormulaProof
    (C := Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (D := FieldCohomologyModule.{u, w} k Ω) (A := AddCommGrpCat.{max u w})
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (fieldInvariantFunctor.{u, w} k Ω)
    (P := Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) q I

/-- The full family preserves the SAME canonical map into degree-zero derived objects. -/
theorem fieldDerivedSectionsInvariantsIso_toRightDerivedZero
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let C := Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}
    let D := FieldCohomologyModule.{u, w} k Ω
    let A := AddCommGrpCat.{max u w}
    let T : C ⥤ D := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    let G : D ⥤ A := fieldInvariantFunctor.{u, w} k Ω
    let P : C ⥤ A := Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}
    let _ : T.Additive := inferInstance
    let _ : T.PreservesInjectiveObjects := inferInstance
    let _ : T.PreservesHomology := inferInstance
    let _ : P.Additive := inferInstance
    let _ : G.Additive := fieldInvariantFunctor_additive.{u, w} k Ω
    let α : P ≅ T ⋙ G := fieldGlobalSectionsInvariantsIso.{u, w} k Ω
    let e : P.rightDerived 0 ≅ T ⋙ G.rightDerived 0 :=
      Functor.rightDerivedPrecompIsoOfIso T G α 0
    (P.toRightDerivedZero.app Q ≫ e.hom.app Q :
        P.obj Q ⟶ (G.rightDerived 0).obj (T.obj Q)) =
      (α.hom.app Q ≫ G.toRightDerivedZero.app (T.obj Q) :
        P.obj Q ⟶ (G.rightDerived 0).obj (T.obj Q)) := by
  exact derivedZeroMapProof
    (C := Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (D := FieldCohomologyModule.{u, w} k Ω) (A := AddCommGrpCat.{max u w})
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (fieldInvariantFunctor.{u, w} k Ω)
    (P := Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) Q

/-- In degree zero this is exactly the previously fixed original section/invariant map. -/
theorem fieldDerivedSectionsInvariantsIso_zero
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldDerivedSectionsInvariantsIso.{u, w} k Ω 0).hom.app Q ≫
        (fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom.app
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) =
      (Sheaf.Γ (Spec (.of k)).smallEtaleTopology
        AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.hom.app Q ≫
        (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q := by
  exact derivedZeroIsoProof
    (C := Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (D := FieldCohomologyModule.{u, w} k Ω) (A := AddCommGrpCat.{max u w})
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (fieldInvariantFunctor.{u, w} k Ω)
    (P := Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) Q

/-- Actual Gamma-resolution homology is identified with the SAME mapped-invariant homology. -/
def fieldDerivedSectionsInvariantsResolutionIso (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :=
  Functor.rightDerivedPrecompHomologyIsoOfIso
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (fieldInvariantFunctor.{u, w} k Ω)
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) q I

/-- Every original bundled map of resolutions gives the SAME literal homology square. -/
theorem fieldDerivedSectionsInvariantsResolutionIso_naturality (q : ℕ)
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {f : Q ⟶ Q'} {I : InjectiveResolution Q} {J : InjectiveResolution Q'}
    (φ : InjectiveResolution.Hom I J f) :
    let C := Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}
    let D := FieldCohomologyModule.{u, w} k Ω
    let A := AddCommGrpCat.{max u w}
    let T : C ⥤ D := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    let G : D ⥤ A := fieldInvariantFunctor.{u, w} k Ω
    let P : C ⥤ A := Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}
    let _ : T.Additive := inferInstance
    let _ : T.PreservesInjectiveObjects := inferInstance
    let _ : T.PreservesHomology := inferInstance
    let _ : P.Additive := inferInstance
    let _ : G.Additive := fieldInvariantFunctor_additive.{u, w} k Ω
    let α : P ≅ T ⋙ G := fieldGlobalSectionsInvariantsIso.{u, w} k Ω
    let H : CochainComplex A ℕ ⥤ A :=
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q
    let I' : InjectiveResolution (T.obj Q) :=
      T.mapInjectiveResolution I
    let J' : InjectiveResolution (T.obj Q') :=
      T.mapInjectiveResolution J
    let K₀ : CochainComplex A ℕ := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let K₀' : CochainComplex A ℕ := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
    let K₁ : CochainComplex A ℕ := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I'.cocomplex
    let K₁' : CochainComplex A ℕ := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj J'.cocomplex
    let eI : H.obj K₀ ≅ H.obj K₁ :=
      Functor.rightDerivedPrecompHomologyIsoOfIso T G α q I
    let eJ : H.obj K₀' ≅ H.obj K₁' :=
      Functor.rightDerivedPrecompHomologyIsoOfIso T G α q J
    (H.map ((P.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) ≫ eJ.hom :
        H.obj K₀ ⟶ H.obj K₁') =
      (eI.hom ≫ H.map ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (T.mapInjectiveResolutionHom φ).hom) : H.obj K₀ ⟶ H.obj K₁') := by
  exact derivedResolutionNaturalityProof
    (C := Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (D := FieldCohomologyModule.{u, w} k Ω) (A := AddCommGrpCat.{max u w})
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (fieldInvariantFunctor.{u, w} k Ω)
    (P := Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) q φ

/-- EVERY canonical comparison of original resolution choices preserves the fixed map. -/
theorem fieldDerivedSectionsInvariantsResolutionIso_comparison (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I J : InjectiveResolution Q) :
    let C := Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}
    let D := FieldCohomologyModule.{u, w} k Ω
    let A := AddCommGrpCat.{max u w}
    let T : C ⥤ D := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    let G : D ⥤ A := fieldInvariantFunctor.{u, w} k Ω
    let P : C ⥤ A := Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}
    let _ : T.Additive := inferInstance
    let _ : T.PreservesInjectiveObjects := inferInstance
    let _ : T.PreservesHomology := inferInstance
    let _ : P.Additive := inferInstance
    let _ : G.Additive := fieldInvariantFunctor_additive.{u, w} k Ω
    let α : P ≅ T ⋙ G := fieldGlobalSectionsInvariantsIso.{u, w} k Ω
    let H : CochainComplex A ℕ ⥤ A :=
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q
    let I' : InjectiveResolution (T.obj Q) :=
      T.mapInjectiveResolution I
    let J' : InjectiveResolution (T.obj Q) :=
      T.mapInjectiveResolution J
    let K₀ : CochainComplex A ℕ := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let K₀' : CochainComplex A ℕ := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
    let K₁ : CochainComplex A ℕ := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I'.cocomplex
    let K₁' : CochainComplex A ℕ := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj J'.cocomplex
    let eI : H.obj K₀ ≅ H.obj K₁ :=
      Functor.rightDerivedPrecompHomologyIsoOfIso T G α q I
    let eJ : H.obj K₀' ≅ H.obj K₁' :=
      Functor.rightDerivedPrecompHomologyIsoOfIso T G α q J
    let a : H.obj K₀ ≅ H.obj K₀' := InjectiveResolution.cohomologyComparisonIso I J P q
    let b : H.obj K₁ ≅ H.obj K₁' := InjectiveResolution.cohomologyComparisonIso I' J' G q
    (a.hom ≫ eJ.hom : H.obj K₀ ⟶ H.obj K₁') =
      (eI.hom ≫ b.hom : H.obj K₀ ⟶ H.obj K₁') := by
  exact derivedResolutionChoiceProof
    (C := Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (D := FieldCohomologyModule.{u, w} k Ω) (A := AddCommGrpCat.{max u w})
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (fieldInvariantFunctor.{u, w} k Ω)
    (P := Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) q I J

/-- The field family agrees with the actual arbitrary-resolution isomorphism. -/
theorem fieldDerivedSectionsInvariantsIso_resolution_iso (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    let C := Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}
    let D := FieldCohomologyModule.{u, w} k Ω
    let A := AddCommGrpCat.{max u w}
    let T : C ⥤ D := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    let G : D ⥤ A := fieldInvariantFunctor.{u, w} k Ω
    let P : C ⥤ A := Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}
    let _ : T.Additive := inferInstance
    let _ : T.PreservesInjectiveObjects := inferInstance
    let _ : T.PreservesHomology := inferInstance
    let _ : P.Additive := inferInstance
    let _ : G.Additive := fieldInvariantFunctor_additive.{u, w} k Ω
    let α : P ≅ T ⋙ G := fieldGlobalSectionsInvariantsIso.{u, w} k Ω
    let H : CochainComplex A ℕ ⥤ A :=
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q
    let I' : InjectiveResolution (T.obj Q) :=
      T.mapInjectiveResolution I
    let K₀ : CochainComplex A ℕ := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let K₂ : CochainComplex A ℕ := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I'.cocomplex
    let e : P.rightDerived q ≅ T ⋙ G.rightDerived q :=
      Functor.rightDerivedPrecompIsoOfIso T G α q
    let a : (P.rightDerived q).obj Q ≅ H.obj K₀ := I.isoRightDerivedObj P q
    let b : H.obj K₀ ≅ H.obj K₂ :=
      Functor.rightDerivedPrecompHomologyIsoOfIso T G α q I
    let c : (G.rightDerived q).obj (T.obj Q) ≅ H.obj K₂ := I'.isoRightDerivedObj G q
    (e.hom.app Q : (P.rightDerived q).obj Q ⟶ (G.rightDerived q).obj (T.obj Q)) =
      (a.hom ≫ b.hom ≫ c.inv :
        (P.rightDerived q).obj Q ⟶ (G.rightDerived q).obj (T.obj Q)) := by
  exact derivedResolutionIsoProof
    (C := Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (D := FieldCohomologyModule.{u, w} k Ω) (A := AddCommGrpCat.{max u w})
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (fieldInvariantFunctor.{u, w} k Ω)
    (P := Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) q I

/-- The actual mapped cocomplex is literally the original cocomplex mapped along T. -/
theorem fieldMappedInjectiveResolution_cocomplex
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    (fieldMappedInjectiveResolution.{u, w} k Ω I).cocomplex =
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex := rfl

/-- The single-object augmentation is the SAME actual single-map comparison and T(I.ι). -/
theorem fieldMappedInjectiveResolution_augmentation
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    (fieldMappedInjectiveResolution.{u, w} k Ω I).ι =
      (HomologicalComplex.singleMapHomologicalComplex
        (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (ComplexShape.up ℕ) 0).inv.app Q ≫
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapHomologicalComplex
          (ComplexShape.up ℕ)).map I.ι := rfl

/-- Injectivity is proved on each actual mapped term, using the accepted equivalence. -/
theorem fieldMappedInjectiveResolution_injective
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) (n : ℕ) :
    Injective ((fieldMappedInjectiveResolution.{u, w} k Ω I).cocomplex.X n) :=
  (fieldMappedInjectiveResolution.{u, w} k Ω I).injective n

/-- The actual augmentation is genuinely a quasi-isomorphism. -/
theorem fieldMappedInjectiveResolution_quasiIso
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    QuasiIso (fieldMappedInjectiveResolution.{u, w} k Ω I).ι :=
  (fieldMappedInjectiveResolution.{u, w} k Ω I).quasiIso

/-- Its literal zero component is the original T-map of the original augmentation. -/
theorem fieldMappedInjectiveResolution_zero
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    (fieldMappedInjectiveResolution.{u, w} k Ω I).ι.f 0 =
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map (I.ι.f 0) :=
  Functor.mapInjectiveResolution_iota_zero (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) I

/-- Every actual source-resolution map is literally mapped by the SAME T. -/
theorem fieldMappedInjectiveResolutionHom_hom
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {f : Q ⟶ Q'} {I : InjectiveResolution Q} {J : InjectiveResolution Q'}
    (φ : InjectiveResolution.Hom I J f) :
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapInjectiveResolutionHom φ).hom =
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapHomologicalComplex
        (ComplexShape.up ℕ)).map φ.hom := rfl

/-- The mapped morphism commutes with the actual full single-object augmentations. -/
theorem fieldMappedInjectiveResolutionHom_augmentation
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {f : Q ⟶ Q'} {I : InjectiveResolution Q} {J : InjectiveResolution Q'}
    (φ : InjectiveResolution.Hom I J f) :
    (fieldMappedInjectiveResolution.{u, w} k Ω I).ι ≫
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapInjectiveResolutionHom φ).hom =
      (HomologicalComplex.single (FieldCohomologyModule.{u, w} k Ω) (ComplexShape.up ℕ) 0).map
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map f) ≫
          (fieldMappedInjectiveResolution.{u, w} k Ω J).ι :=
  ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapInjectiveResolutionHom φ).ι_comp_hom

/-- The actual zero-derived class has exactly its prescribed original section germ. -/
theorem fieldDerivedSectionsInvariantsIso_zero_germ
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (x : ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology
   AddCommGrpCat.{max u w}).rightDerived 0).obj Q) :
    (((fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom.app
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q))
      ((fieldDerivedSectionsInvariantsIso.{u, w} k Ω 0).hom.app Q x)).val =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldIdentityEtale k) (ULift.up (fieldTerminalFiberPoint k Ω)) Q.obj
          ((fieldGammaSectionsIso.{u, w} k).hom.app Q
            ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology
              AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.hom.app Q x)) := by
  have h := ConcreteCategory.congr_hom
    (fieldDerivedSectionsInvariantsIso_zero.{u, w} k Ω Q) x
  exact (congrArg Subtype.val h).trans
    (fieldGlobalSectionsInvariantsIso_germ.{u, w} k Ω Q
      ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology
        AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.hom.app Q x))

/-- Every original coefficient-w sheaf enters the SAME comparison via exactly one L.obj F. -/
def originalFieldDerivedSectionsInvariantsIso (q : ℕ)
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}) :
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q).obj
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≅
      ((fieldInvariantFunctor.{u, w} k Ω).rightDerived q).obj
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) :=
  (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).app
    ((liftCoefficients.{u, w} (Spec (.of k))).obj F)

/-- Every original coefficient arrow uses that SAME single L.map f. -/
theorem originalFieldDerivedSectionsInvariantsIso_naturality (q : ℕ)
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (f : F ⟶ F') :
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q).map
        ((liftCoefficients.{u, w} (Spec (.of k))).map f) ≫
      (originalFieldDerivedSectionsInvariantsIso.{u, w} k Ω q F').hom =
    (originalFieldDerivedSectionsInvariantsIso.{u, w} k Ω q F).hom ≫
      ((fieldInvariantFunctor.{u, w} k Ω).rightDerived q).map
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
          ((liftCoefficients.{u, w} (Spec (.of k))).map f)) :=
  fieldDerivedSectionsInvariantsIso_naturality.{u, w} k Ω q
    ((liftCoefficients.{u, w} (Spec (.of k))).map f)

/-- A native original section is sent to its actual zero-derived Gamma class after one lift. -/
def originalFieldZeroDerivedSection
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (c : F.obj.obj (op (fieldIdentityEtale k))) :
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived 0).obj
      ((liftCoefficients.{u, w} (Spec (.of k))).obj F) :=
  (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).toRightDerivedZero.app
    ((liftCoefficients.{u, w} (Spec (.of k))).obj F)
      ((fieldGammaSectionsIso.{u, w} k).inv.app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F) (ULift.up c))

/-- The original section normalization is exactly the previously accepted invariant coefficient. -/
theorem originalFieldDerivedSectionsInvariantsIso_zero_section
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (c : F.obj.obj (op (fieldIdentityEtale k))) :
    (fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom.app
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F))
      ((originalFieldDerivedSectionsInvariantsIso.{u, w} k Ω 0 F).hom
        (originalFieldZeroDerivedSection.{u, w} k F c)) =
      originalFieldSectionsInvariantsEquiv.{u, w} k Ω F c := by
  let Q := (liftCoefficients.{u, w} (Spec (.of k))).obj F
  let x := (fieldGammaSectionsIso.{u, w} k).inv.app Q (ULift.up c)
  have h := ConcreteCategory.congr_hom
    (Functor.rightDerivedPrecompIsoOfIso_zero_section
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (fieldInvariantFunctor.{u, w} k Ω)
      (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) Q) x
  exact h.trans (originalFieldSectionsInvariantsEquiv_normalization.{u, w} k Ω F c).symm

/-- The normalized original class has the literal original chosen-point germ, with one lift. -/
theorem originalFieldDerivedSectionsInvariantsIso_zero_germ
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (c : F.obj.obj (op (fieldIdentityEtale k))) :
    ((fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom.app
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F))
      ((originalFieldDerivedSectionsInvariantsIso.{u, w} k Ω 0 F).hom
        (originalFieldZeroDerivedSection.{u, w} k F c))).val =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldIdentityEtale k) (ULift.up (fieldTerminalFiberPoint k Ω))
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F).obj (ULift.up c) := by
  exact (congrArg Subtype.val
    (originalFieldDerivedSectionsInvariantsIso_zero_section.{u, w} k Ω F c)).trans
      (originalFieldSectionsInvariantsEquiv_germ.{u, w} k Ω F c)

/-- The original comparison is literally evaluation of the same family at one L.obj F. -/
theorem originalFieldDerivedSectionsInvariantsIso_eq (q : ℕ)
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}) :
    originalFieldDerivedSectionsInvariantsIso.{u, w} k Ω q F =
      (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F) := rfl


/-- The full original source unit fixes the actual family, all resolutions/maps and both
common and original degree-zero section/germ normalizations. -/
structure OriginalFieldDerivedSectionsInvariantsLaws : Prop where
  invariant_left_exact : PreservesFiniteLimits (fieldInvariantFunctor.{u, w} k Ω)
  actual_natural_family : ∀ q : ℕ,
    Nonempty ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q ≅
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        (fieldInvariantFunctor.{u, w} k Ω).rightDerived q)
  family_hom_inv : ∀ (q : ℕ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}),
    (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).hom.app Q ≫
      (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).inv.app Q = 𝟙 _
  family_inv_hom : ∀ (q : ℕ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}),
    (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).inv.app Q ≫
      (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).hom.app Q = 𝟙 _
  all_original_sheaf_maps : ∀ (q : ℕ)
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : Q ⟶ Q'),
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q).map f ≫
          (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).hom.app Q' =
        (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).hom.app Q ≫
          ((fieldInvariantFunctor.{u, w} k Ω).rightDerived q).map
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map f)
  actual_mapped_cocomplex : ∀ {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q),
    (fieldMappedInjectiveResolution.{u, w} k Ω I).cocomplex =
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex
  actual_single_augmentation : ∀
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q),
    (fieldMappedInjectiveResolution.{u, w} k Ω I).ι =
          (HomologicalComplex.singleMapHomologicalComplex
            (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (ComplexShape.up ℕ) 0).inv.app Q ≫
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapHomologicalComplex
              (ComplexShape.up ℕ)).map I.ι
  actual_injective_terms : ∀ {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) (n : ℕ),
    Injective ((fieldMappedInjectiveResolution.{u, w} k Ω I).cocomplex.X n)
  actual_quasi_iso : ∀ {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q),
    QuasiIso (fieldMappedInjectiveResolution.{u, w} k Ω I).ι
  literal_zero_augmentation : ∀
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q),
    (fieldMappedInjectiveResolution.{u, w} k Ω I).ι.f 0 =
          (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map (I.ι.f 0)
  actual_resolution_map : ∀ {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {f : Q ⟶ Q'} {I : InjectiveResolution Q} {J : InjectiveResolution Q'}
    (φ : InjectiveResolution.Hom I J f),
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapInjectiveResolutionHom φ).hom =
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapHomologicalComplex
            (ComplexShape.up ℕ)).map φ.hom
  actual_augmentation_square : ∀
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {f : Q ⟶ Q'} {I : InjectiveResolution Q} {J : InjectiveResolution Q'}
    (φ : InjectiveResolution.Hom I J f),
    (fieldMappedInjectiveResolution.{u, w} k Ω I).ι ≫
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapInjectiveResolutionHom φ).hom =
          (HomologicalComplex.single (FieldCohomologyModule.{u, w} k Ω) (ComplexShape.up ℕ) 0).map
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map f) ≫
              (fieldMappedInjectiveResolution.{u, w} k Ω J).ι
  every_resolution_formula : ∀ (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q),
    let C := Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}
    let D := FieldCohomologyModule.{u, w} k Ω
    let A := AddCommGrpCat.{max u w}
    let T : C ⥤ D := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    let G : D ⥤ A := fieldInvariantFunctor.{u, w} k Ω
    let P : C ⥤ A := Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}
    let _ : T.Additive := inferInstance
    let _ : T.PreservesInjectiveObjects := inferInstance
    let _ : T.PreservesHomology := inferInstance
    let _ : P.Additive := inferInstance
    let _ : G.Additive := fieldInvariantFunctor_additive.{u, w} k Ω
    let α : P ≅ T ⋙ G := fieldGlobalSectionsInvariantsIso.{u, w} k Ω
    let H : CochainComplex A ℕ ⥤ A :=
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q
    let I' : InjectiveResolution (T.obj Q) :=
      T.mapInjectiveResolution I
    let K₀ : CochainComplex A ℕ := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let K₂ : CochainComplex A ℕ := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I'.cocomplex
    let e : P.rightDerived q ≅ T ⋙ G.rightDerived q :=
      Functor.rightDerivedPrecompIsoOfIso T G α q
    let a : (P.rightDerived q).obj Q ≅ H.obj K₀ := I.isoRightDerivedObj P q
    let b : H.obj K₀ ≅ H.obj K₂ :=
      Functor.rightDerivedPrecompHomologyIsoOfIso T G α q I
    let c : (G.rightDerived q).obj (T.obj Q) ≅ H.obj K₂ := I'.isoRightDerivedObj G q
    (e.hom.app Q : (P.rightDerived q).obj Q ⟶ (G.rightDerived q).obj (T.obj Q)) =
      (a.hom ≫ b.hom ≫ c.inv :
        (P.rightDerived q).obj Q ⟶ (G.rightDerived q).obj (T.obj Q))
  every_resolution_map_square : ∀ (q : ℕ)
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {f : Q ⟶ Q'} {I : InjectiveResolution Q} {J : InjectiveResolution Q'}
    (φ : InjectiveResolution.Hom I J f),
    let C := Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}
    let D := FieldCohomologyModule.{u, w} k Ω
    let A := AddCommGrpCat.{max u w}
    let T : C ⥤ D := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    let G : D ⥤ A := fieldInvariantFunctor.{u, w} k Ω
    let P : C ⥤ A := Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}
    let _ : T.Additive := inferInstance
    let _ : T.PreservesInjectiveObjects := inferInstance
    let _ : T.PreservesHomology := inferInstance
    let _ : P.Additive := inferInstance
    let _ : G.Additive := fieldInvariantFunctor_additive.{u, w} k Ω
    let α : P ≅ T ⋙ G := fieldGlobalSectionsInvariantsIso.{u, w} k Ω
    let H : CochainComplex A ℕ ⥤ A :=
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q
    let I' : InjectiveResolution (T.obj Q) :=
      T.mapInjectiveResolution I
    let J' : InjectiveResolution (T.obj Q') :=
      T.mapInjectiveResolution J
    let K₀ : CochainComplex A ℕ := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let K₀' : CochainComplex A ℕ := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
    let K₁ : CochainComplex A ℕ := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I'.cocomplex
    let K₁' : CochainComplex A ℕ := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj J'.cocomplex
    let eI : H.obj K₀ ≅ H.obj K₁ :=
      Functor.rightDerivedPrecompHomologyIsoOfIso T G α q I
    let eJ : H.obj K₀' ≅ H.obj K₁' :=
      Functor.rightDerivedPrecompHomologyIsoOfIso T G α q J
    (H.map ((P.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) ≫ eJ.hom :
        H.obj K₀ ⟶ H.obj K₁') =
      (eI.hom ≫ H.map ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (T.mapInjectiveResolutionHom φ).hom) : H.obj K₀ ⟶ H.obj K₁')
  every_canonical_choice_square : ∀ (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I J : InjectiveResolution Q),
    let C := Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}
    let D := FieldCohomologyModule.{u, w} k Ω
    let A := AddCommGrpCat.{max u w}
    let T : C ⥤ D := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    let G : D ⥤ A := fieldInvariantFunctor.{u, w} k Ω
    let P : C ⥤ A := Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}
    let _ : T.Additive := inferInstance
    let _ : T.PreservesInjectiveObjects := inferInstance
    let _ : T.PreservesHomology := inferInstance
    let _ : P.Additive := inferInstance
    let _ : G.Additive := fieldInvariantFunctor_additive.{u, w} k Ω
    let α : P ≅ T ⋙ G := fieldGlobalSectionsInvariantsIso.{u, w} k Ω
    let H : CochainComplex A ℕ ⥤ A :=
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q
    let I' : InjectiveResolution (T.obj Q) :=
      T.mapInjectiveResolution I
    let J' : InjectiveResolution (T.obj Q) :=
      T.mapInjectiveResolution J
    let K₀ : CochainComplex A ℕ := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let K₀' : CochainComplex A ℕ := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
    let K₁ : CochainComplex A ℕ := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I'.cocomplex
    let K₁' : CochainComplex A ℕ := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj J'.cocomplex
    let eI : H.obj K₀ ≅ H.obj K₁ :=
      Functor.rightDerivedPrecompHomologyIsoOfIso T G α q I
    let eJ : H.obj K₀' ≅ H.obj K₁' :=
      Functor.rightDerivedPrecompHomologyIsoOfIso T G α q J
    let a : H.obj K₀ ≅ H.obj K₀' := InjectiveResolution.cohomologyComparisonIso I J P q
    let b : H.obj K₁ ≅ H.obj K₁' := InjectiveResolution.cohomologyComparisonIso I' J' G q
    (a.hom ≫ eJ.hom : H.obj K₀ ⟶ H.obj K₁') =
      (eI.hom ≫ b.hom : H.obj K₀ ⟶ H.obj K₁')
  same_zero_identification : ∀
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}),
    (fieldDerivedSectionsInvariantsIso.{u, w} k Ω 0).hom.app Q ≫
            (fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom.app
              ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) =
          (Sheaf.Γ (Spec (.of k)).smallEtaleTopology
            AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.hom.app Q ≫
            (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q
  common_original_germ : ∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (x : ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology
   AddCommGrpCat.{max u w}).rightDerived 0).obj Q),
    (((fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom.app
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q))
          ((fieldDerivedSectionsInvariantsIso.{u, w} k Ω 0).hom.app Q x)).val =
          (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
            (fieldIdentityEtale k) (ULift.up (fieldTerminalFiberPoint k Ω)) Q.obj
              ((fieldGammaSectionsIso.{u, w} k).hom.app Q
                ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology
                  AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.hom.app Q x))
  one_original_object : ∀ (q : ℕ)
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}),
    originalFieldDerivedSectionsInvariantsIso.{u, w} k Ω q F =
          (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).app
            ((liftCoefficients.{u, w} (Spec (.of k))).obj F)
  all_original_coefficient_maps : ∀ (q : ℕ)
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (f : F ⟶ F'),
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q).map
            ((liftCoefficients.{u, w} (Spec (.of k))).map f) ≫
          (originalFieldDerivedSectionsInvariantsIso.{u, w} k Ω q F').hom =
        (originalFieldDerivedSectionsInvariantsIso.{u, w} k Ω q F).hom ≫
          ((fieldInvariantFunctor.{u, w} k Ω).rightDerived q).map
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
              ((liftCoefficients.{u, w} (Spec (.of k))).map f))
  original_section_normalization : ∀ (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (c : F.obj.obj (op (fieldIdentityEtale k))),
    (fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom.app
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
              ((liftCoefficients.{u, w} (Spec (.of k))).obj F))
          ((originalFieldDerivedSectionsInvariantsIso.{u, w} k Ω 0 F).hom
            (originalFieldZeroDerivedSection.{u, w} k F c)) =
          originalFieldSectionsInvariantsEquiv.{u, w} k Ω F c
  original_section_germ : ∀ (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (c : F.obj.obj (op (fieldIdentityEtale k))),
    ((fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom.app
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
              ((liftCoefficients.{u, w} (Spec (.of k))).obj F))
          ((originalFieldDerivedSectionsInvariantsIso.{u, w} k Ω 0 F).hom
            (originalFieldZeroDerivedSection.{u, w} k F c))).val =
          (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
            (fieldIdentityEtale k) (ULift.up (fieldTerminalFiberPoint k Ω))
              ((liftCoefficients.{u, w} (Spec (.of k))).obj F).obj (ULift.up c)

/-- The fixed equivalence identifies actual derived Gamma and derived invariants in EVERY
source degree, with every actual resolution and the SAME original section/germ law. -/
theorem original_field_derived_sections_invariants :
    OriginalFieldDerivedSectionsInvariantsLaws.{u, w} k Ω where
  invariant_left_exact := fieldInvariantFunctor_preservesFiniteLimits.{u, w} k Ω
  actual_natural_family := fun q => ⟨fieldDerivedSectionsInvariantsIso.{u, w} k Ω q⟩
  family_hom_inv := fun q Q => (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).hom_inv_id_app Q
  family_inv_hom := fun q Q => (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).inv_hom_id_app Q
  all_original_sheaf_maps := fieldDerivedSectionsInvariantsIso_naturality.{u, w} k Ω
  actual_mapped_cocomplex := fieldMappedInjectiveResolution_cocomplex.{u, w} k Ω
  actual_single_augmentation := fieldMappedInjectiveResolution_augmentation.{u, w} k Ω
  actual_injective_terms := fieldMappedInjectiveResolution_injective.{u, w} k Ω
  actual_quasi_iso := fieldMappedInjectiveResolution_quasiIso.{u, w} k Ω
  literal_zero_augmentation := fieldMappedInjectiveResolution_zero.{u, w} k Ω
  actual_resolution_map := fieldMappedInjectiveResolutionHom_hom.{u, w} k Ω
  actual_augmentation_square := fieldMappedInjectiveResolutionHom_augmentation.{u, w} k Ω
  every_resolution_formula := fieldDerivedSectionsInvariantsIso_resolution_iso.{u, w} k Ω
  every_resolution_map_square := fieldDerivedSectionsInvariantsResolutionIso_naturality.{u, w} k Ω
  every_canonical_choice_square := fieldDerivedSectionsInvariantsResolutionIso_comparison.{u, w} k Ω
  same_zero_identification := fieldDerivedSectionsInvariantsIso_zero.{u, w} k Ω
  common_original_germ := fieldDerivedSectionsInvariantsIso_zero_germ.{u, w} k Ω
  one_original_object := originalFieldDerivedSectionsInvariantsIso_eq.{u, w} k Ω
  all_original_coefficient_maps := originalFieldDerivedSectionsInvariantsIso_naturality.{u, w} k Ω
  original_section_normalization :=
    originalFieldDerivedSectionsInvariantsIso_zero_section.{u, w} k Ω
  original_section_germ := originalFieldDerivedSectionsInvariantsIso_zero_germ.{u, w} k Ω

end AlgebraicGeometry.Scheme.DerivedSections
