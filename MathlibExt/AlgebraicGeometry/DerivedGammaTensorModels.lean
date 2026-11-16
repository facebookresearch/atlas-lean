/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
public import MathlibExt.AlgebraicGeometry.DerivedScalarGlobalSections

/-!
# Actual coefficient cones and the mixed projection formula

The coefficient complex is the actual cofibrant scalar module for
RΓ(X,O_X). Its cone is computed through the normalized full Cech
comparison, after injective replacement. Tensoring that cone with
each de Rham weight gives the projection formula; every affine
projection on every pure generator is fixed.

The relative target is an actual pure-tensor mixed diagram, not a
separately chosen finite-dimensional space. Its source and resolved
diagrams retain every coefficient map and epsilon. Compactness gives
the quasi-isomorphism through a separate proof request.

Reference: PTVV arXiv:1111.3209v4, §2.1, pp.30–32.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open MathlibExt.Algebra.Homology.PureTensorNegativeCyclic
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedScalarUnitModels
open MathlibExt.AlgebraicGeometry.DerivedScalarGlobalSections
open MathlibExt.AlgebraicGeometry.DerivedCompactOrientations
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientCechModels
open MathlibExt.AlgebraicGeometry.DerivedFamilyCoefficientCategories
open MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

universe u
variable {k : Type u} [CommRing k] {N : ShuffleAlgebraFunctor k}
    {S : AffineScalarSystem N} {M : AffineModuleFibration N S} {U : RegularUnitSystem M}
    {Q : AlgebraReplacementFunctor k} {L : CochainLiftModel k} {V : NerveLiftModel L}
    {X : Prestack k} (A : FamilyModel M U Q L V X) (G : QCohEnhancement M U X)
    (D : ScalarGlobalModels A G)

/-- The actual cochain carrier of the cofibrant scalar RΓ module. -/
def gammaCoefficients : Cochains (LargeScalar k) :=
  value (scalarCategory (LargeScalar k)) PUnit.unit D.source.module

/-- Its map to the same actual RΓ is the native augmentation followed by unit evaluation. -/
def gammaAugmentation : gammaCoefficients A G D ⟶ globalHom G G.unit :=
  moduleComponent D.source.augmentation (op PUnit.unit) ≫
    (cochainValueIso D.scalarUnit (globalHom G G.unit) D.evaluation).hom

/-- The complete source coefficient cone retains the injective Cech comparison. -/
def gammaCoefficientCone {C : FamilyCoefficientCategory L N X}
    {F : CoefficientDiagramSystem C G} {B : EnrichedDiagramReplacement C G F}
    {H : CoefficientLimitFunctor C G B} {J : UnitCoefficientDiagram C G F}
    {T : UnitCoefficientLift C G B J} {I : CoherentUnitCone C G T}
    (P : GlobalSectionComparison C G H I) :
    Cone (evaluateDiagram B.diagram G.unit) :=
  (limit.cone (evaluateDiagram B.diagram G.unit)).extend
    (gammaAugmentation A G D ≫ globalSectionMap C G P G.unit)

/-- One source Cech packet retains the native category, all-E replacement,
coherent coefficient unit and every-degree comparison. -/
structure GammaCechData {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {M : AffineModuleFibration N S} {U : RegularUnitSystem M} {X : Prestack k}
    (L : CochainLiftModel k) (G : QCohEnhancement M U X) where
  category : FamilyCoefficientCategory L N X
  source : CoefficientDiagramSystem category G
  replacement : EnrichedDiagramReplacement category G source
  limit : CoefficientLimitFunctor category G replacement
  unit : UnitCoefficientDiagram category G source
  unitLift : UnitCoefficientLift category G replacement unit
  unitCone : CoherentUnitCone category G unitLift
  comparison : GlobalSectionComparison category G limit unitCone

/-- The weight comparison transports only the displayed mixed-object equality. -/
def pureWeightComparison {E : GradedMixed (LargeScalar k)} {C : Cochains (LargeScalar k)}
    (Z : GradedMixed (LargeScalar k)) (P : PureTensorModel E C) (h : Z = P.mixed) (w : ℤ) :
    Z.weight w ≅ E.weight w ⊗ C :=
  eqToIso (congrArg (fun F : GradedMixed (LargeScalar k) => F.weight w) h) ≪≫ P.weightIso w

/-- A tensor mixed diagram has exactly the actual weightwise tensors and scalar maps. -/
structure PureTensorDiagram (E : GradedMixed (LargeScalar k))
    (C : Families X ⥤ Cochains (LargeScalar k)) where
  diagram : Families X ⥤ GradedMixed (LargeScalar k)
  model : ∀ j, PureTensorModel E (C.obj j)
  object : ∀ j, diagram.obj j = (model j).mixed
  map : ∀ (j l : Families X) (f : j ⟶ l) (w : ℤ),
    (diagram.map f).map w ≫ (pureWeightComparison (diagram.obj l) (model l) (object l) w).hom =
      (pureWeightComparison (diagram.obj j) (model j) (object j) w).hom ≫
        (𝟙 (E.weight w) ⊗ₘ C.map f)

/-- Tensor diagram maps use the same coefficient map in every weight. -/
structure PureTensorDiagramMap {E : GradedMixed (LargeScalar k)}
    {C C' : Families X ⥤ Cochains (LargeScalar k)} (f : C ⟶ C')
    (P : PureTensorDiagram E C) (P' : PureTensorDiagram E C') where
  map : P.diagram ⟶ P'.diagram
  normalized : ∀ (j : Families X) (w : ℤ),
    (map.app j).map w ≫ (pureWeightComparison (P'.diagram.obj j) (P'.model j) (P'.object j) w).hom =
      (pureWeightComparison (P.diagram.obj j) (P.model j) (P.object j) w).hom ≫
        (𝟙 (E.weight w) ⊗ₘ f.app j)

/-- A mixed diagram limit has its actual weights and every epsilon projection fixed. -/
structure MixedDiagramLimit (B : Families X ⥤ GradedMixed (LargeScalar k)) where
  mixed : GradedMixed (LargeScalar k)
  weight : ∀ w : ℤ, mixed.weight w ≅ limit (B ⋙ weightFunctor w)
  cone : (Functor.const (Families X)).obj mixed ⟶ B
  normalized : ∀ (j : Families X) (w : ℤ),
    (cone.app j).map w = (weight w).hom ≫ limit.π (B ⋙ weightFunctor w) j

/-- The whole mixed comparison square used by the actual tensor projection formula. -/
structure TensorDiagramLift {E : GradedMixed (LargeScalar k)}
    {C C' : Families X ⥤ Cochains (LargeScalar k)} {f : C ⟶ C'}
    {P : PureTensorDiagram E C} {P' : PureTensorDiagram E C'}
    (K : PureTensorDiagramMap f P P') (B : MixedDiagramReplacement P.diagram) where
  map : P'.diagram ⟶ B.diagram
  square : K.map ≫ map = B.augmentation

/-- An actual pure-tensor map fixes both source factors in every weight. -/
structure PureTensorMap {R : Type u} [CommRing R] {E E' : GradedMixed R} {C C' : Cochains R}
    (f : MixedMap E E') (c : C ⟶ C') (P : PureTensorModel E C) (P' : PureTensorModel E' C') where
  map : MixedMap P.mixed P'.mixed
  normalized : ∀ w : ℤ, map.map w ≫ (P'.weightIso w).hom =
    (P.weightIso w).hom ≫ (f.map w ⊗ₘ c)

/-- The projection-formula map is fixed by the actual resolved coefficient cone
on every homogeneous generator and every affine family. -/
structure ProjectionFormulaMap {E : GradedMixed (LargeScalar k)}
    {C : Families X ⥤ Cochains (LargeScalar k)} (c : Cone C)
    (P : PureTensorDiagram E C) (B : MixedDiagramReplacement P.diagram)
    (H : MixedDiagramLimit B.diagram) (Z : PureTensorModel E c.pt) where
  map : MixedMap Z.mixed H.mixed
  normalized : ∀ (j : Families X) (w p q n : ℤ) (h : p + q = n)
      (e : (E.weight w).X p) (a : c.pt.X q),
    (((map.map w) ≫ (H.cone.app j).map w).f n).hom
      (((Z.weightIso w).inv.f n).hom
        ((HomologicalComplex.ιTensorObj (E.weight w) c.pt p q n h).hom
          (TensorProduct.tmul (LargeScalar k) e a))) =
    (((B.augmentation.app j).map w).f n).hom
      (((pureWeightComparison (P.diagram.obj j) (P.model j) (P.object j) w).inv.f n).hom
        ((HomologicalComplex.ιTensorObj (E.weight w) (C.obj j) p q n h).hom
          (TensorProduct.tmul (LargeScalar k) e ((c.π.app j).f q a))))

end MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
