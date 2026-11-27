/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeRingedIndImageModels
public import MathlibExt.AlgebraicGeometry.ProductDifferentialOperatorModels
public import MathlibExt.CategoryTheory.NativeBoundedDerivedFunctors
public import MathlibExt.CategoryTheory.NativeEnhancedBimoduleQuotients

/-!
# Actual ringed enhanced null images over X times the real compactification

The base image is the actual composite of the product projection inverse
image and real graph inverse image; their point map is pi_X. The boundary
image is the native ringed proper image of the actual closed complement.
Both images act on all original bounded Ind modules. Their exact source
images define the native ringed enhanced quotient.

Source: DK1311.2374v2 Definitions4.10.1,4.10.4 and Section4.4;
Mathlib56a005 native inverse/proper images, bounded Q and trW, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeEnhancedModuleGeometry

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves NativeIndDifferentialContexts NativeIndModuleInverseModels
open NativeRingedIndImageModels ProductDifferentialOperatorModels ProjectiveExponentialSectionModels
open EnhancedIndQuotientModels BorderedIndDerivedModels BoundedIndOperationSources
open MathlibExt.CategoryTheory.NativeRingedAdjointImageModels
open MathlibExt.CategoryTheory.NativeBoundedBimoduleModels
open MathlibExt.CategoryTheory.NativeBoundedDerivedFunctors
open MathlibExt.CategoryTheory.NativeEnhancedBimoduleQuotients
open scoped Manifold ContDiff

variable [∀ Z : TopCat.{0}, HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
  (n : ℕ) (X : Type) [TopologicalSpace X]
  [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) X]
  [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ X]
  [ProjectiveComplexSource]
  [HasSheafify (Opens.grothendieckTopology X) RingCat.{0}]
  [CompactSheafSource ℂ (TopCat.of X)] [IndSpaceSource (TopCat.of X)]
  [DifferentialBetaSource X (analyticCoefficients n X)]
  [CompactSheafSource ℂ (ProductSpace X)] [IndSpaceSource (ProductSpace X)]
  [CompactSheafSource ℂ (enhancedSpace (TopCat.of X)).ambient]
  [IndSpaceSource (enhancedSpace (TopCat.of X)).ambient]
  [CompactSheafSource ℂ (boundarySpace (enhancedSpace (TopCat.of X)))]
  [IndSpaceSource (boundarySpace (enhancedSpace (TopCat.of X)))]
  (Real : RealProjectiveMapSource)
  (First : InverseMonoidalSource (xProjection X))
  (Graph : InverseMonoidalSource (realGraphInclusion (TopCat.of X) Real))

abbrev BaseDX := betaRing (TopCat.of X) (analyticDifferentialRing n X)
abbrev ProductInverseDX := inverseRing (xProjection X) First (BaseDX n X)
abbrev RealInverseDX := inverseRing (realGraphInclusion (TopCat.of X) Real) Graph
  (ProductInverseDX n X First)

local instance geometryModulePreadditive (Z : TopCat.{0})
    [HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
    [CompactSheafSource ℂ Z] [IndSpaceSource Z] (R S : Mon (IndSheaf ℂ Z)) :
    Preadditive (Bimod R S) := Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

/-- Structural proofs refer to the original native images on the exact fixed geometry. -/
structure EnhancedModuleGeometrySource where
  firstImage : IndModuleInverseSource (xProjection X) First (BaseDX n X)
  [firstAdditive : (indModuleInverse (xProjection X) First (BaseDX n X) firstImage).Additive]
  firstExact : ExactImageSource (indModuleInverse (xProjection X) First (BaseDX n X) firstImage)
  firstBounded : BoundedFunctorSource
    (derivedIndModuleInverse (xProjection X) First (BaseDX n X) firstImage firstExact)
  graphImage : IndModuleInverseSource (realGraphInclusion (TopCat.of X) Real) Graph
    (ProductInverseDX n X First)
  [graphAdditive : (indModuleInverse (realGraphInclusion (TopCat.of X) Real) Graph
    (ProductInverseDX n X First) graphImage).Additive]
  graphExact : ExactImageSource (indModuleInverse (realGraphInclusion (TopCat.of X) Real) Graph
    (ProductInverseDX n X First) graphImage)
  graphBounded : BoundedFunctorSource
    (derivedIndModuleInverse (realGraphInclusion (TopCat.of X) Real) Graph
      (ProductInverseDX n X First) graphImage graphExact)
  boundaryInverse : InverseMonoidalSource (boundaryInclusion (enhancedSpace (TopCat.of X)))
  boundaryProper : ProperSource ℂ (boundaryInclusion (enhancedSpace (TopCat.of X)))
  boundaryAdjunction : originalInverse (boundaryInclusion (enhancedSpace (TopCat.of X))) boundaryInverse ⊣
    originalProper (boundaryInclusion (enhancedSpace (TopCat.of X))) boundaryProper
  boundaryImage : RingedIndImageSource (boundaryInclusion (enhancedSpace (TopCat.of X)))
    boundaryInverse boundaryProper boundaryAdjunction (RealInverseDX n X Real First Graph)
  [boundaryAdditive : (originalRingedProper (boundaryInclusion (enhancedSpace (TopCat.of X)))
    boundaryInverse boundaryProper boundaryAdjunction (RealInverseDX n X Real First Graph)
      boundaryImage).Additive]
  boundaryDerivation : RightDerivationSource
    (originalRingedProper (boundaryInclusion (enhancedSpace (TopCat.of X)))
      boundaryInverse boundaryProper boundaryAdjunction (RealInverseDX n X Real First Graph)
        boundaryImage)
  boundaryBounded : BoundedFunctorSource
    (derivedRingedProper (boundaryInclusion (enhancedSpace (TopCat.of X)))
      boundaryInverse boundaryProper boundaryAdjunction (RealInverseDX n X Real First Graph)
        boundaryImage boundaryDerivation)

variable (S : EnhancedModuleGeometrySource n X Real First Graph)

def nativeBaseInverse : BoundedModules (BaseDX n X) (Mon.trivial (IndSheaf ℂ (TopCat.of X))) ⥤
    BoundedModules (RealInverseDX n X Real First Graph)
      (Mon.trivial (IndSheaf ℂ (enhancedSpace (TopCat.of X)).ambient)) :=
  letI := S.firstAdditive
  letI := S.graphAdditive
  boundedFunctor (derivedIndModuleInverse (xProjection X) First (BaseDX n X)
    S.firstImage S.firstExact) S.firstBounded ⋙
    boundedFunctor (derivedIndModuleInverse (realGraphInclusion (TopCat.of X) Real) Graph
      (ProductInverseDX n X First) S.graphImage S.graphExact) S.graphBounded

def nativeBoundaryImage :
    BoundedModules (inverseRing (boundaryInclusion (enhancedSpace (TopCat.of X))) S.boundaryInverse
      (RealInverseDX n X Real First Graph))
      (Mon.trivial (IndSheaf ℂ (boundarySpace (enhancedSpace (TopCat.of X))))) ⥤
    BoundedModules (RealInverseDX n X Real First Graph)
      (Mon.trivial (IndSheaf ℂ (enhancedSpace (TopCat.of X)).ambient)) :=
  letI := S.boundaryAdditive
  boundedFunctor (derivedRingedProper (boundaryInclusion (enhancedSpace (TopCat.of X)))
    S.boundaryInverse S.boundaryProper S.boundaryAdjunction (RealInverseDX n X Real First Graph)
      S.boundaryImage S.boundaryDerivation) S.boundaryBounded

abbrev NativeEnhancedDModules := EnhancedModules (RealInverseDX n X Real First Graph)
  (Mon.trivial (IndSheaf ℂ (enhancedSpace (TopCat.of X)).ambient))
    (nativeBoundaryImage n X Real First Graph S) (nativeBaseInverse n X Real First Graph S)

def nativeModuleQ :
    BoundedModules (RealInverseDX n X Real First Graph)
      (Mon.trivial (IndSheaf ℂ (enhancedSpace (TopCat.of X)).ambient)) ⥤
        NativeEnhancedDModules n X Real First Graph S :=
  moduleQuotient (RealInverseDX n X Real First Graph)
    (Mon.trivial (IndSheaf ℂ (enhancedSpace (TopCat.of X)).ambient))
      (nativeBoundaryImage n X Real First Graph S) (nativeBaseInverse n X Real First Graph S)

end MathlibExt.AlgebraicGeometry.NativeEnhancedModuleGeometry
