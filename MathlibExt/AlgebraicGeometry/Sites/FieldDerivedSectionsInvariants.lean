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

/-!
# Derived sections and invariant resolution coordinates

For a field with prescribed separable closure, the geometric-stalk Galois equivalence
identifies global sections with invariants. With coefficient universe `max u w`, this gives
`R^qΓ ≅ T ⋙ R^q Inv` for every natural degree.

A sheaf injective resolution maps to an injective resolution of its geometric fiber. The
comparison has the specified cochain and coaugmentation maps, factors through resolution
cohomology, and commutes with all resolution morphisms and changes of resolution.

In degree zero the invariant coordinate is the geometric germ of the terminal section.
Coefficient sheaves from universe `w` are lifted to the common universe with the same section
and morphism values.
-/
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

/-- Invariant functor of discrete field coefficients.

Take `Gal(Ω/k)`-invariants of a discrete Galois coefficient, valued in additive groups of the
common universe. -/
abbrev fieldInvariantFunctor : FieldCohomologyModule.{u, w} k Ω ⥤ AddCommGrpCat.{max u w} :=
  DiscreteAbelianAction.invariantsFunctor

/-- Field invariants preserve addition of coefficient maps.

The invariant functor is additive. -/
instance fieldInvariantFunctor_additive : (fieldInvariantFunctor.{u, w} k Ω).Additive where
  map_add {_ _} f g := by
    ext m
    apply Subtype.ext
    rfl

/-- Sections of the inverse sheaf are coefficient invariants.

The invariant inverse-sheaf functor followed by global sections is naturally isomorphic to the
field invariant functor. -/
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

/-- Field invariant functor is a right adjoint.

The invariant functor is right adjoint through its section and inverse-sheaf description. -/
instance fieldInvariantFunctor_isRightAdjoint :
    (fieldInvariantFunctor.{u, w} k Ω).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (fieldInverseGammaInvariantsIso.{u, w} k Ω)

/-- Field invariant functor is left exact.

Field invariants preserve finite limits. -/
instance fieldInvariantFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (fieldInvariantFunctor.{u, w} k Ω) := by infer_instance

/-- Geometric fiber of a sheaf injective resolution.

Apply the geometric-stalk Galois functor to an injective resolution to obtain an injective
resolution of the geometric fiber. -/
abbrev fieldMappedInjectiveResolution
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    InjectiveResolution ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) :=
  (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapInjectiveResolution I

/-- Derived field sections compare with derived invariants.

The global-section invariant coordinate and exact geometric fiber give a natural isomorphism
`R^qΓ ≅ T ⋙ R^q Inv` in every degree. -/
def fieldDerivedSectionsInvariantsIso (q : ℕ) :
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q ≅
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        (fieldInvariantFunctor.{u, w} k Ω).rightDerived q :=
  Functor.rightDerivedPrecompIsoOfIso (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    (fieldInvariantFunctor.{u, w} k Ω) (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) q

/-- Derived section invariant comparison is sheaf natural.

A sheaf map commutes with the comparison and the derived-invariant map of its geometric fiber. -/
theorem fieldDerivedSectionsInvariantsIso_naturality (q : ℕ)
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : Q ⟶ Q') :
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q).map f ≫
      (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).hom.app Q' =
    (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).hom.app Q ≫
      ((fieldInvariantFunctor.{u, w} k Ω).rightDerived q).map
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map f) :=
  (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).hom.naturality f


/-- Resolution formula for the derived section comparison.

The forward comparison is the source resolution coordinate, the homology map of the section-
invariant transformation, the mapped-resolution coordinate, and the inverse target resolution
coordinate. -/
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

/-- Derived section comparison respects the canonical zero degree map.

The canonical map from sections to their zeroth derived functor commutes with the section-
invariant transformation and the zeroth derived-invariant map. -/
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

/-- Derived section comparison has the underived zero coordinate.

In degree zero, the comparison followed by the derived-zero invariant coordinate equals the
derived-zero section coordinate followed by the global-section invariant isomorphism. -/
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

/-- Section and invariant resolution cohomology comparison.

For any sheaf injective resolution, compare cohomology of its sections with invariant
cohomology of the mapped geometric-fiber resolution. -/
def fieldDerivedSectionsInvariantsResolutionIso (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :=
  Functor.rightDerivedPrecompHomologyIsoOfIso
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (fieldInvariantFunctor.{u, w} k Ω)
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) q I

/-- Resolution cohomology comparison respects resolution morphisms.

A resolution morphism over a sheaf map commutes with the section-to-invariant cohomology
coordinates. -/
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

/-- Resolution cohomology comparison respects changes of resolution.

The section and invariant comparison squares commute with the canonical cohomology
isomorphisms between two injective resolutions. -/
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

/-- Derived comparison factors through resolution cohomology.

The forward derived comparison is the source resolution isomorphism, the section-to-invariant
resolution isomorphism, and the inverse mapped-resolution isomorphism. -/
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

/-- Mapped resolution has the geometric fiber cocomplex.

Its underlying cochain complex is the termwise image of the sheaf resolution under the
geometric-stalk Galois functor. -/
theorem fieldMappedInjectiveResolution_cocomplex
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    (fieldMappedInjectiveResolution.{u, w} k Ω I).cocomplex =
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex := rfl

/-- Mapped resolution has the mapped coaugmentation.

The coaugmentation is the inverse single-complex functor coordinate followed by the geometric-
fiber image of the sheaf coaugmentation. -/
theorem fieldMappedInjectiveResolution_augmentation
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    (fieldMappedInjectiveResolution.{u, w} k Ω I).ι =
      (HomologicalComplex.singleMapHomologicalComplex
        (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (ComplexShape.up ℕ) 0).inv.app Q ≫
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapHomologicalComplex
          (ComplexShape.up ℕ)).map I.ι := rfl

/-- Mapped resolution terms are injective.

Every term of the mapped geometric-fiber resolution is injective. -/
theorem fieldMappedInjectiveResolution_injective
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) (n : ℕ) :
    Injective ((fieldMappedInjectiveResolution.{u, w} k Ω I).cocomplex.X n) :=
  (fieldMappedInjectiveResolution.{u, w} k Ω I).injective n

/-- Mapped resolution coaugmentation is a quasi isomorphism.

The mapped coaugmentation is a quasi-isomorphism. -/
theorem fieldMappedInjectiveResolution_quasiIso
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    QuasiIso (fieldMappedInjectiveResolution.{u, w} k Ω I).ι :=
  (fieldMappedInjectiveResolution.{u, w} k Ω I).quasiIso

/-- Mapped resolution coaugmentation retains its degree zero map.

Its degree-zero component is the geometric-stalk Galois image of the sheaf resolution's
degree-zero coaugmentation. -/
theorem fieldMappedInjectiveResolution_zero
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    (fieldMappedInjectiveResolution.{u, w} k Ω I).ι.f 0 =
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map (I.ι.f 0) :=
  Functor.mapInjectiveResolution_iota_zero (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) I

/-- Mapped resolution morphism is the termwise fiber map.

The underlying cochain map of a mapped resolution morphism is the termwise geometric-fiber
image of the given resolution morphism. -/
theorem fieldMappedInjectiveResolutionHom_hom
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {f : Q ⟶ Q'} {I : InjectiveResolution Q} {J : InjectiveResolution Q'}
    (φ : InjectiveResolution.Hom I J f) :
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapInjectiveResolutionHom φ).hom =
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapHomologicalComplex
        (ComplexShape.up ℕ)).map φ.hom := rfl

/-- Mapped resolution morphism respects coaugmentation.

The mapped morphism commutes with the mapped coaugmentations and the single-complex map of the
geometric-fiber coefficient morphism. -/
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

/-- Zero derived section comparison is the terminal geometric germ.

After the derived-zero invariant coordinate, a degree-zero section class has underlying value
the germ of its terminal section at the prescribed geometric point. -/
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

/-- Derived section comparison on lifted coefficient sheaves.

Evaluate the common-universe comparison at a sheaf lifted from coefficient universe `w`. -/
def originalFieldDerivedSectionsInvariantsIso (q : ℕ)
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}) :
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q).obj
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≅
      ((fieldInvariantFunctor.{u, w} k Ω).rightDerived q).obj
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) :=
  (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).app
    ((liftCoefficients.{u, w} (Spec (.of k))).obj F)

/-- Lifted coefficient derived section comparison is natural.

The comparison commutes with the lifted sheaf map and its geometric-fiber derived-invariant
map. -/
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

/-- Terminal section as a degree zero derived class.

Lift the terminal section, use the inverse global-section coordinate, and apply the canonical
map to zeroth derived sections. -/
def originalFieldZeroDerivedSection
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (c : F.obj.obj (op (fieldIdentityEtale k))) :
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived 0).obj
      ((liftCoefficients.{u, w} (Spec (.of k))).obj F) :=
  (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).toRightDerivedZero.app
    ((liftCoefficients.{u, w} (Spec (.of k))).obj F)
      ((fieldGammaSectionsIso.{u, w} k).inv.app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F) (ULift.up c))

/-- Lifted terminal section comparison gives the invariant section value.

The compared derived-zero section, normalized to invariants, equals the terminal-section
invariant equivalence applied to the given section. -/
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

/-- Lifted terminal section comparison gives its geometric germ.

The underlying compared invariant element is the common geometric germ of the lifted terminal
section. -/
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

/-- Lifted sheaf comparison is evaluation of the common family.

The lifted-sheaf isomorphism is the component of the common-universe derived section
comparison at the lifted sheaf. -/
theorem originalFieldDerivedSectionsInvariantsIso_eq (q : ℕ)
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}) :
    originalFieldDerivedSectionsInvariantsIso.{u, w} k Ω q F =
      (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F) := rfl


/-- Full resolution and section laws of the derived comparison.

These laws record left exact invariants, the natural comparison and inverse identities, mapped
resolutions and their maps, resolution formulas and choices, zero coordinates, and lifted-
section values. -/
structure OriginalFieldDerivedSectionsInvariantsLaws : Prop where
/-- Derived section law fixes left exact invariants.

The invariant functor preserves finite limits. -/
  invariant_left_exact : PreservesFiniteLimits (fieldInvariantFunctor.{u, w} k Ω)
/-- Derived section law supplies every degree comparison.

For every natural degree there is the natural isomorphism from derived sections to derived
invariants of the geometric fiber. -/
  actual_natural_family : ∀ q : ℕ,
    Nonempty ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q ≅
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        (fieldInvariantFunctor.{u, w} k Ω).rightDerived q)
/-- Derived section law gives the forward inverse identity.

For every degree and sheaf, forward comparison followed by inverse comparison is the identity. -/
  family_hom_inv : ∀ (q : ℕ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}),
    (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).hom.app Q ≫
      (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).inv.app Q = 𝟙 _
/-- Derived section law gives the inverse forward identity.

For every degree and sheaf, inverse comparison followed by forward comparison is the identity. -/
  family_inv_hom : ∀ (q : ℕ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}),
    (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).inv.app Q ≫
      (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).hom.app Q = 𝟙 _
/-- Derived section law retains all sheaf map squares.

The comparison commutes with every sheaf map and its geometric-fiber derived-invariant map. -/
  all_original_sheaf_maps : ∀ (q : ℕ)
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : Q ⟶ Q'),
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q).map f ≫
          (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).hom.app Q' =
        (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).hom.app Q ≫
          ((fieldInvariantFunctor.{u, w} k Ω).rightDerived q).map
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map f)
/-- Derived section law fixes the mapped resolution complex.

The mapped resolution's cocomplex is the termwise geometric-fiber image of the given sheaf
cocomplex. -/
  actual_mapped_cocomplex : ∀ {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q),
    (fieldMappedInjectiveResolution.{u, w} k Ω I).cocomplex =
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex
/-- Derived section law fixes the single coaugmentation coordinate.

The mapped coaugmentation is the inverse single-complex coordinate followed by the mapped
sheaf coaugmentation. -/
  actual_single_augmentation : ∀
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q),
    (fieldMappedInjectiveResolution.{u, w} k Ω I).ι =
          (HomologicalComplex.singleMapHomologicalComplex
            (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (ComplexShape.up ℕ) 0).inv.app Q ≫
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapHomologicalComplex
              (ComplexShape.up ℕ)).map I.ι
/-- Derived section law gives injective mapped terms.

Each term of every mapped resolution is injective. -/
  actual_injective_terms : ∀ {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) (n : ℕ),
    Injective ((fieldMappedInjectiveResolution.{u, w} k Ω I).cocomplex.X n)
/-- Derived section law gives the mapped quasi isomorphism.

Each mapped resolution coaugmentation is a quasi-isomorphism. -/
  actual_quasi_iso : ∀ {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q),
    QuasiIso (fieldMappedInjectiveResolution.{u, w} k Ω I).ι
/-- Derived section law fixes the zero coaugmentation map.

The mapped coaugmentation in degree zero is the fiber image of the given degree-zero map. -/
  literal_zero_augmentation : ∀
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q),
    (fieldMappedInjectiveResolution.{u, w} k Ω I).ι.f 0 =
          (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map (I.ι.f 0)
/-- Derived section law fixes every mapped resolution morphism.

Every mapped resolution morphism has the termwise image cochain map. -/
  actual_resolution_map : ∀ {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {f : Q ⟶ Q'} {I : InjectiveResolution Q} {J : InjectiveResolution Q'}
    (φ : InjectiveResolution.Hom I J f),
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapInjectiveResolutionHom φ).hom =
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapHomologicalComplex
            (ComplexShape.up ℕ)).map φ.hom
/-- Derived section law gives every coaugmentation square.

Each mapped resolution morphism commutes with its coaugmentations and the mapped coefficient
arrow. -/
  actual_augmentation_square : ∀
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {f : Q ⟶ Q'} {I : InjectiveResolution Q} {J : InjectiveResolution Q'}
    (φ : InjectiveResolution.Hom I J f),
    (fieldMappedInjectiveResolution.{u, w} k Ω I).ι ≫
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapInjectiveResolutionHom φ).hom =
          (HomologicalComplex.single (FieldCohomologyModule.{u, w} k Ω) (ComplexShape.up ℕ) 0).map
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map f) ≫
              (fieldMappedInjectiveResolution.{u, w} k Ω J).ι
/-- Derived section law retains every resolution factorization.

For every resolution and degree, the forward derived comparison factors through its section
and invariant cohomology coordinates. -/
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
/-- Derived section law retains every resolution map square.

Every resolution morphism commutes with the section-to-invariant cohomology comparison. -/
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
/-- Derived section law retains every resolution choice square.

The comparison commutes with the canonical cohomology isomorphisms of any pair of resolutions. -/
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
/-- Derived section law fixes the zero degree identification.

The zeroth derived comparison agrees with the underived section-invariant coordinate through
the derived-zero isomorphisms. -/
  same_zero_identification : ∀
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}),
    (fieldDerivedSectionsInvariantsIso.{u, w} k Ω 0).hom.app Q ≫
            (fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom.app
              ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) =
          (Sheaf.Γ (Spec (.of k)).smallEtaleTopology
            AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.hom.app Q ≫
            (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q
/-- Derived section law fixes the common terminal germ.

The normalized zero-degree comparison has underlying value the common geometric germ of its
terminal section. -/
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
/-- Derived section law identifies each lifted sheaf component.

The lifted-sheaf comparison is the common natural family's component at that sheaf. -/
  one_original_object : ∀ (q : ℕ)
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}),
    originalFieldDerivedSectionsInvariantsIso.{u, w} k Ω q F =
          (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q).app
            ((liftCoefficients.{u, w} (Spec (.of k))).obj F)
/-- Derived section law retains all lifted coefficient maps.

The lifted-sheaf comparison commutes with every coefficient sheaf morphism. -/
  all_original_coefficient_maps : ∀ (q : ℕ)
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (f : F ⟶ F'),
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q).map
            ((liftCoefficients.{u, w} (Spec (.of k))).map f) ≫
          (originalFieldDerivedSectionsInvariantsIso.{u, w} k Ω q F').hom =
        (originalFieldDerivedSectionsInvariantsIso.{u, w} k Ω q F).hom ≫
          ((fieldInvariantFunctor.{u, w} k Ω).rightDerived q).map
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
              ((liftCoefficients.{u, w} (Spec (.of k))).map f))
/-- Derived section law normalizes lifted terminal sections.

The normalized invariant value of a lifted degree-zero section is its section-invariant
equivalence value. -/
  original_section_normalization : ∀ (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (c : F.obj.obj (op (fieldIdentityEtale k))),
    (fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom.app
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
              ((liftCoefficients.{u, w} (Spec (.of k))).obj F))
          ((originalFieldDerivedSectionsInvariantsIso.{u, w} k Ω 0 F).hom
            (originalFieldZeroDerivedSection.{u, w} k F c)) =
          originalFieldSectionsInvariantsEquiv.{u, w} k Ω F c
/-- Derived section law retains lifted section germs.

The underlying invariant value is the common geometric germ of the lifted terminal section. -/
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

/-- Derived field sections satisfy their full invariant comparison laws.

The comparison satisfies all naturality, inverse, mapped-resolution, coaugmentation,
resolution-choice, and terminal-section normalization laws. -/
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
