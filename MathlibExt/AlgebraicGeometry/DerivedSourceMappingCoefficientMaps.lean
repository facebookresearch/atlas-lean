/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedSourceMappingTangents

/-!
# Actual affine RΓ evaluation comparison from the native adjunction mate

The coefficient map is the native base-change mate: pull the global
pushforward counit through the actual affine product square, then
transpose under the all-degree X_A projection adjunction. Applying Hom
from the actual coefficient unit gives RΓ_X_A of the literal evaluation
pullback. Every comparison is of full DG functors and is normalized on
the original structure unit. No independent Gamma endpoint map is used.

Source: PTVV arXiv:1111.3209v4, proof of Theorem 2.5, pp.33--35;
HAG II arXiv:math/0404373v7, Section 1.4.1. Native notices remain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedSourceMappingCoefficientMaps

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedCotangentDifferentials
open MathlibExt.AlgebraicGeometry.DerivedCompactOrientations
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
open MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
open MathlibExt.AlgebraicGeometry.DerivedSourcedCechModels
open MathlibExt.AlgebraicGeometry.DerivedSymplecticContractions
open MathlibExt.AlgebraicGeometry.DerivedCotangentFormSources
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedSourceMappingTangents
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

universe u
variable {k : Type u} [CommRing k] [Algebra ℚ k]
    {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {NC : MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams.NegativeCyclicDiagram
      D.functor (2 : ℤ)} {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {M : AffineModuleFibration N S} {U : RegularUnitSystem M}
    {R : RawModuleRealization M} {L : CochainLiftModel k} {V : NerveLiftModel L}
    {X F : Prestack k} {RF : FibrantReplacement F}
    (E : EvaluationModel Q X F RF)
    (B : MappingTangentSources (U := U) (R := R) (L := L) (D := D) (NC := NC) E)
    (BX : FamilyModel M U Q L V X) (A : SAlg k)
    (f : affineMapping k Q A ⟶ mappingPrestackFunctor k Q X F RF)

/-- The source square is made of actual complete DG pullback functors and original coefficient units. -/
structure AffineMappingGammaSources where
  spec : CoefficientQCohEnhancement M U Q L V A (BX.affine A) (affineMapping k Q A) (𝟙 _)
  specCech : GammaCechData L spec.model
  specSource : SourceEnrichedQCohModel specCech.category spec.model R specCech.source specCech.unit
  point : PullbackDGModel f B.mapping.global spec.model
  pointUnit : point.functor.obj B.mapping.global.unit = spec.model.unit
  inclusion : PullbackDGModel (f ⊗ₘ 𝟙 X) B.product (BX.model A)
  inclusionUnit : inclusion.functor.obj B.product.unit = (BX.model A).unit
  projection : PullbackDGModel (productProjection (affineMapping k Q A) X) spec.model (BX.model A)
  projectionUnit : projection.functor.obj spec.model.unit = (BX.model A).unit
  projectionScalar : spec.scalar.functor.comp (Cochains (LargeScalar k)) projection.functor =
    (BX.scalar A).functor
  pushforward : MappingPushforward projection
  evaluation : PullbackDGModel (affineMappingEvaluation E A f) B.target.global (BX.model A)
  evaluationUnit : evaluation.functor.obj B.target.global.unit = (BX.model A).unit
  square : (⟨point.functor.comp (Cochains (LargeScalar k)) projection.functor⟩ :
      DGFunctor (LargeScalar k) B.mapping.global.category (BX.model A).category) ⟶
    (⟨B.projection.functor.comp (Cochains (LargeScalar k)) inclusion.functor⟩ :
      DGFunctor (LargeScalar k) B.mapping.global.category (BX.model A).category)
  squareUnit : square.dgApp B.mapping.global.unit = dgClosedHom (LargeScalar k)
    (eqToHom (congrArg (ForgetEnrichment.of (Cochains (LargeScalar k)))
      (((congrArg projection.functor.obj pointUnit).trans projectionUnit).trans
        ((congrArg inclusion.functor.obj B.mappingPair.unit).trans inclusionUnit).symm)))
  squareWeak : ∀ W : B.mapping.global.category,
    IsShiftedEquivalence (inclusion.functor.obj (B.projection.functor.obj W))
      (projection.functor.obj (point.functor.obj W)) 0 (square.dgApp W)
      ((mem_dgCycles (LargeScalar k)).mp (square.dgApp_mem_dgCycles W))
  evaluationSquare : (⟨B.evaluation.functor.comp (Cochains (LargeScalar k)) inclusion.functor⟩ :
      DGFunctor (LargeScalar k) B.target.global.category (BX.model A).category) ⟶
    (⟨evaluation.functor⟩ : DGFunctor (LargeScalar k) B.target.global.category (BX.model A).category)
  evaluationSquareUnit : evaluationSquare.dgApp B.target.global.unit = dgClosedHom (LargeScalar k)
    (eqToHom (congrArg (ForgetEnrichment.of (Cochains (LargeScalar k)))
      (((congrArg inclusion.functor.obj B.targetPair.unit).trans inclusionUnit).trans evaluationUnit.symm)))
  evaluationSquareWeak : ∀ W : B.target.global.category,
    IsShiftedEquivalence (evaluation.functor.obj W) (inclusion.functor.obj (B.evaluation.functor.obj W))
      0 (evaluationSquare.dgApp W)
      ((mem_dgCycles (LargeScalar k)).mp (evaluationSquare.dgApp_mem_dgCycles W))

/-- The global counit is computed by the inverse of the actual all-degree adjunction. -/
def globalEvaluationCounit : DGHom (LargeScalar k) 0
    (B.projection.functor.obj (evaluationGamma E B))
    (B.evaluation.functor.obj B.target.tangent.object) :=
  (((B.pushforward.hom (evaluationGamma E B)
    (B.evaluation.functor.obj B.target.tangent.object)).inv.f 0).hom
      (dgId (LargeScalar k) (evaluationGamma E B)))

/-- The actual pulled counit is composed with the full affine pullback-square comparisons. -/
def affineEvaluationMate (C : AffineMappingGammaSources E B BX A f) : DGHom (LargeScalar k) 0
    (C.projection.functor.obj (C.point.functor.obj (evaluationGamma E B)))
    (C.evaluation.functor.obj B.target.tangent.object) :=
  dgComp (LargeScalar k) (p := 0) (q := 0) (n := 0)
    (dgComp (LargeScalar k) (p := 0) (q := 0) (n := 0)
      (C.square.dgApp (evaluationGamma E B))
      (C.inclusion.functor.dgMap 0 (globalEvaluationCounit E B)) (by omega))
    (C.evaluationSquare.dgApp B.target.tangent.object) (by omega)

/-- Coefficient base change is the native projection-adjoint transpose of that computed mate. -/
def affineGammaComparison (C : AffineMappingGammaSources E B BX A f) : DGHom (LargeScalar k) 0
    (C.point.functor.obj (evaluationGamma E B))
    (C.pushforward.functor.obj (C.evaluation.functor.obj B.target.tangent.object)) :=
  (((C.pushforward.hom (C.point.functor.obj (evaluationGamma E B))
    (C.evaluation.functor.obj B.target.tangent.object)).hom.f 0).hom (affineEvaluationMate E B BX A f C))

/-- The actual coefficient-module value is the same source RHom from its original unit. -/
def specGammaValueIso (C : AffineMappingGammaSources E B BX A f) (W : C.spec.model.category) :
    value (coefficientLarge L N A) (coefficientObject L N A)
      (globalModule C.spec.scalar W) ≅ globalHom C.spec.model W :=
  eqToIso (by
    dsimp only [value, globalModule, EnrichedFunctor.comp, EnrichedFunctor.op, globalHom, coefficientObject]
    rw [C.spec.scalar.unit_value]
    rfl)

/-- Hom from the original coefficient unit computes the actual RΓ_X_A map of this same adjunction mate. -/
def affineGammaValueMap (C : AffineMappingGammaSources E B BX A f)
    (h : dgDifferential (LargeScalar k) 0 (affineGammaComparison E B BX A f C) = 0) :
    value (coefficientLarge L N A) (coefficientObject L N A)
      (globalModule C.spec.scalar (C.point.functor.obj (evaluationGamma E B))) ⟶
    value (coefficientLarge L N A) (coefficientObject L N A)
      (gamma BX A (C.evaluation.functor.obj B.target.tangent.object)) :=
  (specGammaValueIso E B BX A f C _).hom ≫
    eHomWhiskerLeft (Cochains (LargeScalar k)) (ForgetEnrichment.of _ C.spec.model.unit)
      (dgClosedHomOf (LargeScalar k) (affineGammaComparison E B BX A f C)
        ((mem_dgCycles (LargeScalar k)).mpr h)) ≫
    (C.pushforward.hom C.spec.model.unit (C.evaluation.functor.obj B.target.tangent.object)).inv ≫
    eqToHom (by rw [C.projectionUnit]; rfl) ≫
    (gammaValueIso BX A (C.evaluation.functor.obj B.target.tangent.object)).inv

/-- Native A-linearity and closure are construction outputs for the fixed computed coefficient map. -/
structure AffineGammaModuleMap (C : AffineMappingGammaSources E B BX A f) where
  closed : dgDifferential (LargeScalar k) 0 (affineGammaComparison E B BX A f C) = 0
  map : globalModule C.spec.scalar (C.point.functor.obj (evaluationGamma E B)) ⟶
    gamma BX A (C.evaluation.functor.obj B.target.tangent.object)
  normalized : moduleComponent map (Opposite.op (coefficientObject L N A)) =
    affineGammaValueMap E B BX A f C closed

end MathlibExt.AlgebraicGeometry.DerivedSourceMappingCoefficientMaps
