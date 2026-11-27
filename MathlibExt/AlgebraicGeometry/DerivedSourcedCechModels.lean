/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedCoefficientCechModels
public import MathlibExt.AlgebraicGeometry.DerivedFamilyDerivations

/-!
# Source normalized QCoh coefficient realizations

The native section category contains all semilinear coefficient actions.
Cofibrancy and every enriched Hom comparison are checked in that actual
module category. This controls positive DG Hom degrees as well as the
categorical nerve. A categorical realization alone would not do so.

Each object has an augmentation to its actual small affine module
diagram. Its geometric class is fixed by the entire raw-module
localization and an equivalence in the category of QCoh sections.
The unit augmentation respects every homogeneous coefficient action.

References: PTVV arXiv:1111.3209v4, Definition 2.1 and pp.30–31;
Keller, Deriving DG categories, §§1 and 6; HAG II math/0404373v7,
§§1.3.7 and 1.4.1. Generic source assembly remains separate Wanted work.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedSourcedCechModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open CochainComplex.HomComplex
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedFamilyCoefficientCategories
open MathlibExt.AlgebraicGeometry.DerivedCoefficientCechModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedCotangentModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k] {L : CochainLiftModel k}
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {M : AffineModuleFibration N S} {U : RegularUnitSystem M} {X : Prestack k}
    (C : FamilyCoefficientCategory L N X)

/-- Projective cofibrancy in the actual DG coefficient-section category,
tested against all componentwise trivial fibrations. -/
def IsCofibrantSection (E : CoefficientSection C) : Prop :=
  letI := C.enrichment
  ∀ (A B : CoefficientSection C) (p : A ⟶ B),
    (∀ j : Families X, QuasiIso (evaluationMap p j) ∧
      ∀ n : ℤ, Function.Surjective ((evaluationMap p j).f n)) →
    ∀ f : E ⟶ B, ∃ g : E ⟶ A, g ≫ p = f

/-- Actual regular coefficient modules, with every arrow-labelled action
fixed by native covariant Yoneda postcomposition and its Koszul sign. -/
structure RegularCoefficientSection where
  sectionModel : CoefficientSection C
  value : letI := C.enrichment
    ∀ j : Families X, sectionModel.toEnrichedFunctor.obj j ≅
    affineCoefficient L N ((algebraProjection X).obj j)
  action : letI := C.enrichment
    ∀ (j l : Families X) (f : j ⟶ l) (p q r : ℤ) (h : q + p = r)
      (a : (affineCoefficient L N ((algebraProjection X).obj l)).X p)
      (m : (affineCoefficient L N ((algebraProjection X).obj j)).X q),
    ((value l).hom.f r).hom
      (((sectionModel.toEnrichedFunctor.dgMap p (generator C f p a) : Cochain _ _ p).v q r h).hom
        (((value j).inv.f q).hom m)) =
      (q * p).negOnePow • dgComp (LargeScalar k)
        (((affineCoefficientMap L N ((algebraProjection X).map f)).f q).hom m) a h

/-- The literal lifted coefficient diagram of a small semilinear module family. -/
def rawCoefficientDiagram (D : Families X ⥤ AffineModulePoint N) :
    Families X ⥤ Cochains (LargeScalar k) :=
  D ⋙ coefficientProjection N ⋙ largeCochainLift k

variable (G : QCohEnhancement M U X) (R : RawModuleRealization M)
    (D : CoefficientDiagramSystem C G)

/-- An object's geometric class is fixed on the entire actual raw family diagram.
The source resolution may be larger and need only augment by quasi-isomorphisms. -/
structure ActualCoefficientSection (E : G.category) where
  raw : Families X ⥤ AffineModulePoint N
  base : raw ⋙ moduleProjection N = algebraProjection X
  object : (qcoh M X) _⦋0⦌
  normalized : (SimplicialCategory.homEquiv' (nerve (Families X)) M.total).symm object.val =
    nerveMap raw ≫ R.map
  equivalence : (qcoh M X) _⦋1⦌
  source : (qcoh M X).δ 1 equivalence = object
  target : (qcoh M X).δ 0 equivalence = G.realization.app (op ⦋0⦌) (objectVertex E)
  weak : IsEquivalenceEdge (qcoh M X) equivalence
  augmentation : evaluateDiagram D.diagram E ⟶ rawCoefficientDiagram raw
  quasi : ∀ j : Families X, QuasiIso (augmentation.app j)
  action : letI := C.enrichment
    ∀ (j l : Families X) (f : j ⟶ l) (p q r : ℤ) (h : q + p = r)
      (a : (N.functor.obj ((algebraProjection X).obj l)).X.X p)
      (m : ((D.sections.obj E).toEnrichedFunctor.obj j).X q),
    HEq
      (((augmentation.app l).f r).hom
        (((eqToHom (D.value E l).symm).f r).hom
          (((D.sections.obj E).toEnrichedFunctor.dgMap p
            (generator C f p (ULift.up a)) : Cochain _ _ p).v q r h m)))
      (ULift.up.{u + 1} (moduleAction (raw.obj l).module (op PUnit.unit)
        (((N.functor.map (eqToHom
          (congrArg (fun F => F.obj l) base).symm)).hom.f p).hom a) h
        (((raw.map f).map.f q).hom
          ((((augmentation.app j).f q).hom
            ((eqToHom (D.value E j).symm).f q m)).down))))

/-- A full enriched source model, including the genuine coefficient unit.
The Hom condition rules out hidden positive-degree data in a bare nerve model. -/
structure SourceEnrichedQCohModel (V : UnitCoefficientDiagram C G D) where
  cofibrant : ∀ E : G.category, IsCofibrantSection C (D.sections.obj E)
  hom : letI := C.enrichment
    ∀ E F : G.category, QuasiIso (D.sections.map E F)
  geometric : ∀ E : G.category, ActualCoefficientSection C G R D E
  regular : RegularCoefficientSection C
  unitAugmentation : letI := C.enrichment
    (D.sections.obj G.unit) ⟶ regular.sectionModel
  unitQuasi : letI := C.enrichment
    ∀ j : Families X, QuasiIso (evaluationMap unitAugmentation j)
  unit_normalized : letI := C.enrichment
    ∀ j : Families X,
    HEq (V.augmentation.app j)
      (eqToHom (D.value G.unit j) ≫ evaluationMap unitAugmentation j ≫
        (regular.value j).hom ≫ eqToHom (V.value j).symm)

end MathlibExt.AlgebraicGeometry.DerivedSourcedCechModels
