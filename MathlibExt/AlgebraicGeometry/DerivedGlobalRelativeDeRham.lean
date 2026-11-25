/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedRelativeAffineDiagrams
public import MathlibExt.AlgebraicGeometry.DerivedClosedFormTransgression

/-!
# Actual global relative de Rham class

The source is the full tensor-affine family diagram. Its relative map
is fixed by the source simplicial product generators and actual
coefficient augmentations. The global product cone is restricted by
the literal tensor-family functor.

The target projection formula is the actual projective tensor-diagram
class computed from native form and coherent RΓ coefficient cones.
The relative global map is fixed by a square in the localization of
whole mixed diagrams. Integration's relative class is its composite
with the inverse projection formula. Neither a global Kunneth
isomorphism nor an independently selected form-producing map is used.

Reference: PTVV arXiv:1111.3209v4, §2.1, pp.30–32.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedGlobalRelativeDeRham

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open MathlibExt.Algebra.Homology.PureTensorNegativeCyclic
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedTensorAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedScalarGlobalSections
open MathlibExt.AlgebraicGeometry.DerivedCompactOrientations
open MathlibExt.AlgebraicGeometry.DerivedCoefficientCechModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
open MathlibExt.AlgebraicGeometry.DerivedMixedLocalizationModels
open MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
open MathlibExt.AlgebraicGeometry.DerivedProjectiveTensorDiagrams
open MathlibExt.AlgebraicGeometry.DerivedRelativeAffineDiagrams
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

universe u
variable {k : Type u} [CommRing k] {Q : AlgebraReplacementFunctor k}
    {D : AffineDRSystem Q} {L : CochainLiftModel k} {T : MixedLiftModel L}
    {F X : Prestack k}

/-- The actual raw form diagram of the first tensor-family projection. -/
def rawForms (D : AffineDRSystem Q) (T : MixedLiftModel L) (F X : Prestack k) :=
  first F X ⋙ algebraProjection F ⋙ D.functor ⋙ T.functor

/-- The resolved form diagram is the same native global mixed replacement. -/
def resolvedForms (G : GlobalMixedModel D T F) (X : Prestack k) :=
  first F X ⋙ G.replacement.diagram

/-- The actual form augmentation is pulled back along the first family projection. -/
def formAugmentation (G : GlobalMixedModel D T F) (X : Prestack k) :
    rawForms D T F X ⟶ resolvedForms G X :=
  Functor.whiskerLeft (first F X) G.replacement.augmentation

/-- The form cone retains every tensor-family simplex through the first projection. -/
def formCone (G : GlobalMixedModel D T F) (X : Prestack k) :
    (Functor.const (TensorFamilies F X)).obj G.mixed ⟶ resolvedForms G X where
  app j := (globalMixedCone G).app ((first F X).obj j)
  naturality _ _ f := (globalMixedCone G).naturality ((first F X).map f)

variable {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {M : AffineModuleFibration N S} {U : RegularUnitSystem M} {V : NerveLiftModel L}
    (B : FamilyModel M U Q L V X) (GX : QCohEnhancement M U X)
    (SC : ScalarGlobalModels B GX) (C : GammaCechData L GX)

/-- The raw coefficient diagram is the actual source RΓ-unit module family. -/
def rawCoefficients (F : Prestack k) :=
  second F X ⋙ evaluateDiagram C.source.diagram GX.unit

/-- The resolved coefficient diagram retains the full Cech injective replacement. -/
def resolvedCoefficients (F : Prestack k) :=
  second F X ⋙ evaluateDiagram C.replacement.diagram GX.unit

/-- The actual coefficient augmentation is pulled back along the second family projection. -/
def coefficientAugmentation (F : Prestack k) :
    rawCoefficients GX C F ⟶ resolvedCoefficients GX C F :=
  Functor.whiskerLeft (second F X) (evaluateDiagramMap C.replacement.augmentation GX.unit)

/-- The genuine coefficient cone is the native cofibrant RΓ augmentation
followed by the complete coherent Cech comparison. -/
def coefficientCone (F : Prestack k) :
    (Functor.const (TensorFamilies F X)).obj (gammaCoefficients B GX SC) ⟶
      resolvedCoefficients GX C F where
  app j := (gammaCoefficientCone B GX SC C.comparison).π.app ((second F X).obj j)
  naturality _ _ f :=
    (gammaCoefficientCone B GX SC C.comparison).π.naturality ((second F X).map f)

/-- The full actual projective tensor source of the global projection formula. -/
abbrev GlobalProjectionDiagram (G : GlobalMixedModel D T F)
    (P : PureTensorModel G.mixed (gammaCoefficients B GX SC)) :=
  ProjectionFormulaDiagram (formAugmentation G X) (coefficientAugmentation GX C F)
    (formCone G X) (coefficientCone B GX SC C F) P

/-- The global product cone is restricted by the actual product chart functor. -/
def productCone (G : GlobalMixedModel D T (F ⊗ X)) :
    (Functor.const (TensorFamilies F X)).obj G.mixed ⟶ product F X ⋙ G.replacement.diagram where
  app j := (globalMixedCone G).app ((product F X).obj j)
  naturality _ _ f := (globalMixedCone G).naturality ((product F X).map f)

/-- The raw source class is the native product cone through the actual product comparison. -/
def rawProductClass {R : ProductReplacementSystem Q}
    (A : RelativeAffineFamilyDiagram D R F X) (G : GlobalMixedModel D T (F ⊗ X))
    (weak : ∀ (j : TensorFamilies F X) (w : ℤ),
      QuasiIso (((liftedProductComparison A G).app j).map w)) :
    (mixedDiagramQ (LargeScalar k) (TensorFamilies F X)).obj
        ((Functor.const (TensorFamilies F X)).obj G.mixed) ⟶
      (mixedDiagramQ (LargeScalar k) (TensorFamilies F X)).obj (A.diagram ⋙ T.functor) := by
  letI := (mixedDiagramWeakEquivalences (LargeScalar k) (TensorFamilies F X)).Q_inverts
    (liftedProductComparison A G) weak
  exact (mixedDiagramQ (LargeScalar k) (TensorFamilies F X)).map (productCone G) ≫
    inv ((mixedDiagramQ (LargeScalar k) (TensorFamilies F X)).map (liftedProductComparison A G))

/-- Complete source normalization of the global relative class. The two
global maps are fixed by actual whole-diagram squares, before weighted NC. -/
structure GlobalRelativeModel (R : ProductReplacementSystem Q) (SL : StrongCochainLift L)
    (G : GlobalMixedModel D T F) (GP : GlobalMixedModel D T (F ⊗ X))
    (P : PureTensorModel G.mixed (gammaCoefficients B GX SC)) where
  projectionDiagram : GlobalProjectionDiagram B GX SC C G P
  raw : RelativeAffineFamilyDiagram D R F X
  coefficientTarget : TensorMixedDiagram (rawForms D T F X) (second F X ⋙ C.unit.coefficients)
  affineRelative : LiftedRelativeFamilyDiagram D R T SL N F X raw C.unit.coefficients
    C.unit.value coefficientTarget
  productWeak : ∀ (j : TensorFamilies F X) (w : ℤ),
    QuasiIso (((liftedProductComparison raw GP).app j).map w)
  coefficientTargetReplacement : MixedDiagramReplacement coefficientTarget.diagram
  unitMap : TensorDiagramMap (𝟙 (rawForms D T F X))
    (Functor.whiskerLeft (second F X) C.unit.augmentation) projectionDiagram.raw coefficientTarget
  unitLift : projectionDiagram.replacement.diagram ⟶ coefficientTargetReplacement.diagram
  unitSquare : projectionDiagram.replacement.augmentation ≫ unitLift =
    unitMap.map ≫ coefficientTargetReplacement.augmentation
  limit : MixedLimitModel projectionDiagram.replacement.diagram
  relative : MixedMap GP.mixed limit.mixed
  relative_normalized :
    (mixedDiagramQ (LargeScalar k) (TensorFamilies F X)).map
      ((Functor.const (TensorFamilies F X)).map relative ≫ limit.cone ≫ unitLift) =
    rawProductClass raw GP productWeak ≫
      (mixedDiagramQ (LargeScalar k) (TensorFamilies F X)).map
        (affineRelative.map ≫ coefficientTargetReplacement.augmentation)
  projection : ProjectionFormulaRealization projectionDiagram limit

/-- The global κ class is exactly relative projection followed by inverse projection formula. -/
def globalKappa {R : ProductReplacementSystem Q} {SL : StrongCochainLift L}
    {G : GlobalMixedModel D T F} {GP : GlobalMixedModel D T (F ⊗ X)}
    {P : PureTensorModel G.mixed (gammaCoefficients B GX SC)}
    (A : GlobalRelativeModel B GX SC C R SL G GP P)
    (weak : ∀ w : ℤ, QuasiIso (A.projection.map.map w)) :
    (mixedQ (LargeScalar k)).obj GP.mixed ⟶ (mixedQ (LargeScalar k)).obj P.mixed := by
  letI := (mixedWeakEquivalences (LargeScalar k)).Q_inverts A.projection.map weak
  exact (mixedQ (LargeScalar k)).map A.relative ≫ inv ((mixedQ (LargeScalar k)).map A.projection.map)

end MathlibExt.AlgebraicGeometry.DerivedGlobalRelativeDeRham
