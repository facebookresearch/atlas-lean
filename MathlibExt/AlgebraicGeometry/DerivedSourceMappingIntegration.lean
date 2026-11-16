/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedSourceMappingTangents
public import MathlibExt.AlgebraicGeometry.DerivedGlobalNCIntegration
public import MathlibExt.AlgebraicGeometry.DerivedSourcedOrientations

/-!
# Source orientation, actual integral and mapping transgression

The integral is the already defined globalIntegrationClass of the
original relative de Rham coefficient diagram, both native NC limit
bridges, the actual finite-coefficient NC tensor comparison, and the
actual scalar trace of degree -d. Its cochain representative has that
computed class. Transgression is literal evaluation pullback followed
by that integral, with output degree n-d.

The nondegeneracy proof is separate and uses the source O-compactness
and all-A perfect-complex orientation pairing. No transgressed
symplectic structure or tangent equivalence is a construction input.

Source: PTVV arXiv:1111.3209v4, Definitions 2.1--2.4 and Theorem 2.5,
pp.30--35. Native mixed/NC, tensor, scalar and license notices remain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedSourceMappingIntegration

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedCompactOrientations
open MathlibExt.AlgebraicGeometry.DerivedOrientationModels
open MathlibExt.AlgebraicGeometry.DerivedSourcedOrientations
open MathlibExt.AlgebraicGeometry.DerivedScalarGlobalSections
open MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
open MathlibExt.AlgebraicGeometry.DerivedMixedLocalizationModels
open MathlibExt.AlgebraicGeometry.DerivedRelativeAffineDiagrams
open MathlibExt.AlgebraicGeometry.DerivedGlobalRelativeDeRham
open MathlibExt.AlgebraicGeometry.DerivedGlobalNCIntegration
open MathlibExt.AlgebraicGeometry.DerivedClosedFormTransgression
open MathlibExt.AlgebraicGeometry.DerivedCotangentFormSources
open MathlibExt.AlgebraicGeometry.DerivedSourceMappingTangents
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open MathlibExt.Algebra.Homology.PureTensorNegativeCyclic
open MathlibExt.Algebra.Homology.ShiftedTensorUnits

universe u
variable {k : Type u} [CommRing k] [Algebra ℚ k]
    {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {NC : NegativeCyclicDiagram D.functor (2 : ℤ)} {N : ShuffleAlgebraFunctor k}
    {S : AffineScalarSystem N} {M : AffineModuleFibration N S} {U : RegularUnitSystem M}
    {R : RawModuleRealization M} {L : CochainLiftModel k} {V : NerveLiftModel L}
    {X F : Prestack k} {RF : FibrantReplacement F}
    (E : EvaluationModel Q X F RF)
    (B : MappingTangentSources (U := U) (R := R) (L := L) (D := D) (NC := NC) E)
    (BX : SourcedScalarFamily M U R Q L V X) {d : ℤ}
    (trace : TraceSystem BX.family.model BX.absolute BX.scalar d)
attribute [local instance] HasDerivedCategory.standard

/-- Every construction is an actual source operator. Comparison proofs concern
the displayed source maps and are returned by the source constructor. -/
structure MappingIntegrationSources where
  lift : MixedLiftModel L
  productReplacement : ProductReplacementSystem Q
  strongLift : StrongCochainLift L
  mappingMixed : GlobalMixedModel D lift (mappingPrestackFunctor k Q X F RF)
  productMixed : GlobalMixedModel D lift (mappingPrestackFunctor k Q X F RF ⊗ X)
  tensor : PureTensorModel mappingMixed.mixed (gammaCoefficients BX.family.model BX.absolute BX.scalar)
  relative : GlobalRelativeModel BX.family.model BX.absolute BX.scalar BX.gamma
    productReplacement strongLift mappingMixed productMixed tensor
  projectionWeak : ∀ w : ℤ, QuasiIso (relative.projection.map.map w)
  ncCategory : NCCategoryModel (LargeScalar k) (2 : ℤ)
  tensorComparison : Comparison tensor (2 : ℤ)
    (ncCategory.diagram.toModel mappingMixed.mixed) (ncCategory.diagram.toModel tensor.mixed)
  [tensorComparisonIso : IsIso (DerivedCategory.Q.map tensorComparison.map)]
  shift : UnitTensorModel (ncCategory.diagram.complex.obj mappingMixed.mixed) (-d)
  productForms : GlobalNCModel D 2 NC (mappingPrestackFunctor k Q X F RF ⊗ X)
  productNC : GlobalNCData productMixed productForms
  mappingNC : GlobalNCData mappingMixed B.mapping.forms
  [mappingNCIso : IsIso (DerivedCategory.Q.map
    ((shiftFunctor (Cochains (LargeScalar k)) (-d)).map (mappingNC.comparison ncCategory)))]
  representative : NCIntegrationRepresentative productForms B.mapping.forms d
    (globalIntegrationClass BX.family.model BX.absolute BX.scalar BX.gamma relative projectionWeak
      ncCategory tensorComparison trace shift productNC mappingNC)

/-- The degree n-d source form is the literal normalized evaluation/integration composite. -/
def sourceMappingTransgressForm (I : MappingIntegrationSources E B BX trace)
    (n : ℤ) (ω : SourceClosedForm B.target n) : SourceClosedForm B.mapping (n - d) := by
  letI := I.tensorComparisonIso
  letI := I.mappingNCIso
  exact transgressForm E B.target.forms I.representative n ω

end MathlibExt.AlgebraicGeometry.DerivedSourceMappingIntegration
