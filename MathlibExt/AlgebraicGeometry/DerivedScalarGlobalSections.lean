/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedScalarUnitModels
public import MathlibExt.AlgebraicGeometry.DerivedCoefficientDualModels

/-!
# Actual scalar extension of global structure sections

The absolute global Hom is RHom(O_X,O_X) in the full QCoh enhancement.
Its base-change map is computed by the actual DG pullback along
X×Spec(A)→X, with the same structure unit. Scalar extension is its
transpose under the native enriched adjunction and both actual module
augmentations. Regular-unit extension uses the actual coefficient unit
map. This fixes the k-linear trace and every A-linear realization.

No invertibility or orientation theorem is included in the model.
Those proofs and coherent assembly remain separate Wanted requests.
Reference: PTVV arXiv:1111.3209v4, §2.1, pp.30--33.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedScalarGlobalSections

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.NativeDGNerveModels
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedCompactOrientations
open MathlibExt.AlgebraicGeometry.DerivedScalarUnitModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientDualModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalSectionBaseChange
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N} {M : AffineModuleFibration N S}
    {U : RegularUnitSystem M} {Q : AlgebraReplacementFunctor k} {L : CochainLiftModel k}
    {V : NerveLiftModel L} {X : Prestack k}

/-- The actual projection X×Spec(A)→X retains every parameter simplex. -/
def sourceProjection (Q : AlgebraReplacementFunctor k) (X : Prestack k) (A : SAlg k) :
    baseChanged Q X A ⟶ X where
  app B := { app _n := ↾fun x => x.2, naturality _ _ _ := rfl }
  naturality _ _ _ := by ext n x; rfl

/-- The absolute-to-relative RΓ source is the actual structure-unit-preserving DG pullback. -/
structure ProjectionModel (B : FamilyModel M U Q L V X) (G : QCohEnhancement M U X) where
  functor : ∀ A : SAlg k, G.category ⟶ (B.model A).category
  normalized : ∀ A : SAlg k,
    (categoricalQ.{u}).map (dgNerveMap (functor A) ≫ (B.model A).realization) =
      (categoricalQ.{u}).map (G.realization ≫ qcohPullback M (sourceProjection Q X A))
  unit_eq : ∀ A : SAlg k, (functor A).obj G.unit = (B.model A).unit

/-- This cochain map is the literal pullback of the absolute global unit Hom. -/
def projectionGamma (B : FamilyModel M U Q L V X) {G : QCohEnhancement M U X}
    (P : ProjectionModel B G) (A : SAlg k) :
    globalHom G G.unit ⟶ value (coefficientLarge L N A) (coefficientObject L N A)
      (gamma B A (B.model A).unit) :=
  (P.functor A).map G.unit G.unit ≫ eqToHom (by rw [P.unit_eq A]; rfl) ≫
    (gammaValueIso B A (B.model A).unit).inv

/-- The selector's coefficient cochain map is the actual enriched identity/unit. -/
def coefficientUnitMap (A : SAlg k)
    (I : UnitFunctorModel (R := LargeScalar k) (coefficientLarge L N A) (coefficientObject L N A)) :
    value (scalarCategory (LargeScalar k)) PUnit.unit
        (regularModule (scalarCategory (LargeScalar k)) PUnit.unit) ⟶
      value (coefficientLarge L N A) (coefficientObject L N A)
        (regularModule (coefficientLarge L N A) (coefficientObject L N A)) :=
  I.functor.map PUnit.unit PUnit.unit ≫ eqToHom (by rw [I.object_eq]; rfl)

/-- A regular-unit extension is fixed by the actual unit coefficient map and adjunction. -/
structure RegularExtensionModel (A : SAlg k)
    (I : UnitFunctorModel (R := LargeScalar k) (coefficientLarge L N A) (coefficientObject L N A))
    (h : IsCofibrantModule (regularModule (scalarCategory (LargeScalar k)) PUnit.unit))
    (R : RestrictionModel I.functor) (D : ExtensionModel I.functor R) where
  unit : DGHom (LargeScalar k) 0
    (regularModule (scalarCategory (LargeScalar k)) PUnit.unit)
    (R.functor.obj (regularModule (coefficientLarge L N A) (coefficientObject L N A)))
  unit_closed : dgDifferential (LargeScalar k) 0 unit = 0
  unit_normalized : ∀ (n : ℤ)
    (m : (value (scalarCategory (LargeScalar k)) PUnit.unit
      (regularModule (scalarCategory (LargeScalar k)) PUnit.unit)).X n),
    ((restrictionPointValueIso I.functor (I.object_eq PUnit.unit) R _).hom.f n).hom
      (mapValue (scalarCategory (LargeScalar k)) PUnit.unit unit (add_zero n) m) =
        ((coefficientUnitMap A I).f n).hom m
  map : DGHom (LargeScalar k) 0
    (D.functor.obj (⟨regularModule (scalarCategory (LargeScalar k)) PUnit.unit, h⟩ :
      DGDerivedModules (LargeScalar k) (scalarCategory (LargeScalar k)))).obj
    (regularModule (coefficientLarge L N A) (coefficientObject L N A))
  closed : dgDifferential (LargeScalar k) 0 map = 0
  normalized : ((D.homIso
    ⟨regularModule (scalarCategory (LargeScalar k)) PUnit.unit, h⟩
    (regularModule (coefficientLarge L N A) (coefficientObject L N A))).hom.f 0).hom map = unit

/-- Source-normalized scalar module data retain actual RΓ and both augmentation maps. -/
structure ScalarGlobalModels (B : FamilyModel M U Q L V X) (G : QCohEnhancement M U X) where
  projection : ProjectionModel B G
  scalarUnit : UnitFunctorModel (R := LargeScalar k) (Cochains (LargeScalar k))
    (𝟙_ (Cochains (LargeScalar k)))
  evaluation : UnitEvaluationModel (globalHom G G.unit)
  source : ModuleReplacement (cochainModule scalarUnit (globalHom G G.unit))
  target : ∀ A : SAlg k, ModuleReplacement (gamma B A (B.model A).unit)
  regular : IsCofibrantModule (regularModule (scalarCategory (LargeScalar k)) PUnit.unit)
  coefficientUnit : ∀ A : SAlg k,
    UnitFunctorModel (R := LargeScalar k) (coefficientLarge L N A) (coefficientObject L N A)
  restriction : ∀ A : SAlg k, RestrictionModel (coefficientUnit A).functor
  extension : ∀ A : SAlg k, ExtensionModel (coefficientUnit A).functor (restriction A)
  baseChange : ∀ A : SAlg k,
    EnrichedModuleBaseChangeModel (scalarCategory (LargeScalar k)) (coefficientLarge L N A)
      PUnit.unit (coefficientObject L N A) (coefficientUnit A).functor
      ((coefficientUnit A).object_eq PUnit.unit) source (target A) (restriction A) (extension A)
      ((cochainValueIso scalarUnit (globalHom G G.unit) evaluation).hom ≫ projectionGamma B projection A)
  regularExtension : ∀ A : SAlg k,
    RegularExtensionModel A (coefficientUnit A) regular (restriction A) (extension A)

end MathlibExt.AlgebraicGeometry.DerivedScalarGlobalSections
