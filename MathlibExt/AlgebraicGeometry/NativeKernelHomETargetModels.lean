/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeKernelReconstructionModels

/-!
# Computed native ringed reconstruction and scalar enhanced-Hom targets

The kernel is an object of the actual source enhanced D-module quotient.
Its coefficient image is computed by native localization of the full
coefficient forgetful functor, with every map fixed by factorization.
The compared target is the original beta-pi/module-tensor-Hom target;
endpoint aliases must equal these exact computed native objects.
Hom^E is literally alpha Rpi_* RIhom(LE,RE). Both objects are computed from that ringed target, without a general scalar-tensor Hom^E
adjunction. Specializing to the computed O^E gives the source target of
Proposition9.5.1; only the separate actual-O reconstruction map has the
holonomic IsIso request.

Source: DK1311.2374v2 Definition4.5.13, Proposition9.5.1, Theorem9.5.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeKernelHomETargetModels

open MathlibExt.AlgebraicGeometry NativeKernelReconstructionModels

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves NativeIndDifferentialContexts NativeIndModuleInverseModels
open NativeEnhancedModuleGeometry NativeBetaModuleDerivedModels NativeEnhancedKernelFunctorModels
open ProjectiveExponentialSectionModels ProductDifferentialOperatorModels
open BorderedIndDerivedModels EnhancedIndQuotientModels EnhancedConvolutionModels
open BoundedIndOperationSources
open MathlibExt.CategoryTheory.NativeRingedAdjointImageModels
open MathlibExt.CategoryTheory.NativeBoundedBimoduleModels
open MathlibExt.CategoryTheory.NativeEnhancedBimoduleQuotients
open MathlibExt.CategoryTheory.NativeDerivedBimoduleCalculus
open MathlibExt.CategoryTheory.NativeRingedReconstructionMaps
open scoped Manifold ContDiff

variable [∀ Z : TopCat.{0}, HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
  (n : ℕ) (X : Type) [TopologicalSpace X] [T2Space X]
  [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) X]
  [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ X]
  [ProjectiveComplexSource]
  [HasSheafify (Opens.grothendieckTopology X) RingCat.{0}]
  [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [CompactSheafSource ℂ (TopCat.of X)] [IndSpaceSource (TopCat.of X)]
  [DifferentialBetaSource X (analyticCoefficients n X)]
  [OppositeDifferentialBetaSource X (analyticCoefficients n X)]
  [CompactSheafSource ℂ (ProductSpace X)] [IndSpaceSource (ProductSpace X)]
  [CompactSheafSource ℂ (enhancedSpace (TopCat.of X)).ambient]
  [IndSpaceSource (enhancedSpace (TopCat.of X)).ambient]
  [CompactSheafSource ℂ (boundarySpace (enhancedSpace (TopCat.of X)))]
  [IndSpaceSource (boundarySpace (enhancedSpace (TopCat.of X)))]
  (Real : RealProjectiveMapSource) (First : InverseMonoidalSource (xProjection X))
  (Graph : InverseMonoidalSource (realGraphInclusion (TopCat.of X) Real))
  (Geometry : EnhancedModuleGeometrySource n X Real First Graph)

local instance reconstructionIndPreadditive (Z : TopCat.{0}) [CompactSheafSource ℂ Z] :
    Preadditive (IndSheaf ℂ Z) := Abelian.toPreadditive
local instance reconstructionModulePreadditive (Z : TopCat.{0})
    [HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
    [CompactSheafSource ℂ Z] [IndSpaceSource Z] (R S : Mon (IndSheaf ℂ Z)) :
    Preadditive (Bimod R S) := Abelian.toPreadditive
local instance reconstructionOrdinaryPreadditive :
    Preadditive (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)) := Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

variable (N : OrdinaryBetaModuleSource (TopCat.of X) (analyticDifferentialRing n X))
  (Normalize : BetaUnitNormalizationSource (TopCat.of X) (analyticDifferentialRing n X))
  [(betaUnitModules (TopCat.of X) (analyticDifferentialRing n X) N Normalize).Additive]
  (BetaExact : ExactImageSource (betaUnitModules (TopCat.of X) (analyticDifferentialRing n X) N Normalize))
  (Representatives : ModuleRepresentativeSource (RY n X Real First Graph) (KY X)
    (nativeBoundaryImage n X Real First Graph Geometry) (nativeBaseInverse n X Real First Graph Geometry))
  (Kernel : NativeEnhancedDModules n X Real First Graph Geometry)
  [LeftTensorDerivationSource (RY n X Real First Graph) (KY X) (KY X)]
  [LeftTensorHomSource (RY n X Real First Graph) (KY X) (KY X)]
  [(Bimod.forget (B := KY X) (KY X)).Additive]
  (CoefficientExact : ExactCoefficientSource (KY X) (KY X))
  (CoefficientBounded : BoundedCoefficientSource (KY X) (KY X) CoefficientExact)
  (Boundary : ProperSource ℂ (boundaryInclusion (enhancedSpace (TopCat.of X))))
  (Projection : InverseSource ℂ (baseProjection (TopCat.of X)))


variable
  [(coefficientEnhancedQ X CoefficientExact CoefficientBounded Boundary Projection).IsRightAdjoint]


variable [∀ H : BoundedModules (KY X) (KY X),
    ((boundedCoefficientTensor n X Real First Graph).obj H).IsLeftAdjoint]
  [(originalOrdinaryBetaPull n X Real First Graph Geometry N Normalize BetaExact).IsLeftAdjoint]
  (M : DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
    (analyticDifferentialRing n X)))
  (BoundedSolution : IsBoundedDerived (Bimod (KY X) (KY X))
    ((solutionsWithKernel n X Real First Graph Geometry N Normalize BetaExact
      Representatives Kernel).obj (Opposite.op M)))



open EnhancedSheafHomModels IndSheafDerivedAlphaModels

local instance wantedKernelOrdinarySheafPreadditive :
    Preadditive (OrdinarySheaf ℂ (TopCat.of X)) := Abelian.toPreadditive

variable [N.forget.functor.Additive]
  (ForgetExact : ExactImageSource N.forget.functor)
  [(Bimod.forget (B := KY X) (RY n X Real First Graph)).Additive]
  (ModuleExact : ExactCoefficientSource (RY n X Real First Graph) (KY X))
  (ModuleBounded : BoundedCoefficientSource (RY n X Real First Graph) (KY X) ModuleExact)


variable (Factor : ModuleCoefficientQuotientSource (RY n X Real First Graph) (KY X)
    (nativeBoundaryImage n X Real First Graph Geometry) (nativeBaseInverse n X Real First Graph Geometry)
    (moduleCoefficientQuotientInput n X Real First Graph Boundary Projection ModuleExact ModuleBounded))
  (AmbientTensor : TensorSource ℂ (enhancedSpace (TopCat.of X)).ambient)
  (HomRepresentatives : EnhancedRepresentativeSource ℂ (TopCat.of X) Boundary Projection)
  (HomClosed : AmbientIhomSource ℂ (TopCat.of X) AmbientTensor)
  (Pi : ProperSource ℂ (baseProjection (TopCat.of X)))
  [(IndSheafAlphaBetaModels.alpha ℂ (TopCat.of X)
    (IndSpaceSource.alpha (X := TopCat.of X))).Additive]
  (AlphaExact : ExactAlphaSource ℂ (TopCat.of X) (IndSpaceSource.alpha (X := TopCat.of X)))


/-- Original native ringed reconstruction target with every complex coefficient map fixed. -/
def reconstructionCoefficientsTarget : OrdinaryDerived ℂ (TopCat.of X) :=
  (derivedExactImage N.forget.functor ForgetExact).obj
      (originalReconstructionTarget n X Real First Graph Geometry N Normalize BetaExact Representatives
      Kernel CoefficientExact CoefficientBounded Boundary Projection M BoundedSolution)

/-- Literal alpha Rpi_* RIhom(LE source solutions, RE kernel coefficient image). -/
def scalarHomETarget : OrdinaryDerived ℂ (TopCat.of X) :=
  (((homE ℂ (TopCat.of X) Boundary Projection AmbientTensor Pi
      (IndSpaceSource.alpha (X := TopCat.of X)) AlphaExact HomRepresentatives HomClosed).obj
      (Opposite.op ((coefficientEnhancedQ X CoefficientExact CoefficientBounded Boundary Projection).obj
      (sourceSolution n X Real First Graph Geometry N Normalize BetaExact Representatives
      Kernel M BoundedSolution)))).obj
      ((moduleCoefficientFunctor n X Real First Graph Geometry Boundary Projection
      ModuleExact ModuleBounded Factor).obj Kernel))

end MathlibExt.AlgebraicGeometry.NativeKernelHomETargetModels
