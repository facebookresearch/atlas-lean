/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeEnhancedKernelFunctorModels
public import MathlibExt.AlgebraicGeometry.EnhancedSheafHomModels
public import MathlibExt.CategoryTheory.NativeRingedReconstructionMaps
public import MathlibExt.CategoryTheory.NativeBoundedBimoduleModels

/-!
# Original native D-module reconstruction evaluation and its source mates

The source solution is actual left-D module Hom. Evaluation is the
original native counit in the endpoint D-module category. L^E Q maps to
that source by the counit of L^E ⊣ Q; no quotient unit is assumed
invertible.
The first mate uses the ambient coefficient tensor/module Hom; the
second uses the actual beta-pull/ringed-projection adjunction. The final
ordinary D-module map is computed here. Its IsIso under holonomicity is
a separate Wanted output, never an assumption about this map.

Source: DK1311.2374v2 Proposition9.5.1 and Theorem9.5.3;
Mathlib56a005 native units, evaluation, tensor/Hom and adjunction mates, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeKernelReconstructionModels

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

def coefficientEnhancedQ : BoundedModules (KY X) (KY X) ⥤
    EnhancedCategory ℂ (TopCat.of X) Boundary Projection :=
  boundedCoefficients (KY X) (KY X) CoefficientExact CoefficientBounded ⋙
    enhancedSourceProjection ℂ (TopCat.of X) Boundary Projection

/-- The actual bounded D-module coefficient forgetful functor followed by the fixed enhanced quotient. -/
def moduleCoefficientQuotientInput
    [(Bimod.forget (B := KY X) (RY n X Real First Graph)).Additive]
    (E : ExactCoefficientSource (RY n X Real First Graph) (KY X))
    (B : BoundedCoefficientSource (RY n X Real First Graph) (KY X) E) :
    BoundedModules (RY n X Real First Graph) (KY X) ⥤
      EnhancedCategory ℂ (TopCat.of X) Boundary Projection :=
  boundedCoefficients (RY n X Real First Graph) (KY X) E B ⋙
    enhancedSourceProjection ℂ (TopCat.of X) Boundary Projection

/-- Its descent uses exactly inversion of the native boundary/pi-image module weak maps. -/
def moduleCoefficientFunctor
    [(Bimod.forget (B := KY X) (RY n X Real First Graph)).Additive]
    (E : ExactCoefficientSource (RY n X Real First Graph) (KY X))
    (B : BoundedCoefficientSource (RY n X Real First Graph) (KY X) E)
    (F : ModuleCoefficientQuotientSource (RY n X Real First Graph) (KY X)
      (nativeBoundaryImage n X Real First Graph Geometry) (nativeBaseInverse n X Real First Graph Geometry)
      (moduleCoefficientQuotientInput n X Real First Graph Boundary Projection E B)) :
    NativeEnhancedDModules n X Real First Graph Geometry ⥤
      EnhancedCategory ℂ (TopCat.of X) Boundary Projection :=
  enhancedModuleCoefficients (RY n X Real First Graph) (KY X)
    (nativeBoundaryImage n X Real First Graph Geometry) (nativeBaseInverse n X Real First Graph Geometry)
      (moduleCoefficientQuotientInput n X Real First Graph Boundary Projection E B) F

/-- Native localization factorization fixes every module coefficient object and map. -/
def moduleCoefficientComparison
    [(Bimod.forget (B := KY X) (RY n X Real First Graph)).Additive]
    (E : ExactCoefficientSource (RY n X Real First Graph) (KY X))
    (B : BoundedCoefficientSource (RY n X Real First Graph) (KY X) E)
    (F : ModuleCoefficientQuotientSource (RY n X Real First Graph) (KY X)
      (nativeBoundaryImage n X Real First Graph Geometry) (nativeBaseInverse n X Real First Graph Geometry)
      (moduleCoefficientQuotientInput n X Real First Graph Boundary Projection E B)) :
    nativeModuleQ n X Real First Graph Geometry ⋙
      moduleCoefficientFunctor n X Real First Graph Geometry Boundary Projection E B F ≅
        moduleCoefficientQuotientInput n X Real First Graph Boundary Projection E B :=
  Localization.fac (moduleCoefficientQuotientInput n X Real First Graph Boundary Projection E B)
    F.inverts (moduleQuotient (RY n X Real First Graph) (KY X)
      (nativeBoundaryImage n X Real First Graph Geometry) (nativeBaseInverse n X Real First Graph Geometry))

/-- The original bordered coefficient category kills the actual closed-boundary image. -/
abbrev coefficientBorderedCategory :=
  letI := Boundary.additive
  BorderedDerived ℂ (enhancedSpace (TopCat.of X)) Boundary.compact Boundary.ind Boundary.derived

/-- Forget all D actions before passing through that actual bordered coefficient quotient. -/
def coefficientBorderedProjection
    [(Bimod.forget (B := KY X) (RY n X Real First Graph)).Additive]
    (E : ExactCoefficientSource (RY n X Real First Graph) (KY X))
    (B : BoundedCoefficientSource (RY n X Real First Graph) (KY X) E) :
    BoundedModules (RY n X Real First Graph) (KY X) ⥤ coefficientBorderedCategory X Boundary :=
  letI := Boundary.additive
  boundedCoefficients (RY n X Real First Graph) (KY X) E B ⋙
    BorderedIndDerivedModels.quotient ℂ (enhancedSpace (TopCat.of X))
      Boundary.compact Boundary.ind Boundary.derived

variable
  [(coefficientEnhancedQ X CoefficientExact CoefficientBounded Boundary Projection).IsRightAdjoint]

def coefficientLeftRepresentative : EnhancedCategory ℂ (TopCat.of X) Boundary Projection ⥤
    BoundedModules (KY X) (KY X) :=
  (coefficientEnhancedQ X CoefficientExact CoefficientBounded Boundary Projection).leftAdjoint

def coefficientRightRepresentative
    [(coefficientEnhancedQ X CoefficientExact CoefficientBounded Boundary
      Projection).IsLeftAdjoint] :
    EnhancedCategory ℂ (TopCat.of X) Boundary Projection ⥤
    BoundedModules (KY X) (KY X) :=
  (coefficientEnhancedQ X CoefficientExact CoefficientBounded Boundary Projection).rightAdjoint

def coefficientLeftAdjunction : coefficientLeftRepresentative X CoefficientExact CoefficientBounded
    Boundary Projection ⊣ coefficientEnhancedQ X CoefficientExact CoefficientBounded Boundary Projection :=
  Adjunction.ofIsRightAdjoint (coefficientEnhancedQ X CoefficientExact CoefficientBounded Boundary Projection)

def coefficientRightAdjunction
    [(coefficientEnhancedQ X CoefficientExact CoefficientBounded Boundary
      Projection).IsLeftAdjoint] :
    coefficientEnhancedQ X CoefficientExact CoefficientBounded Boundary Projection ⊣
    coefficientRightRepresentative X CoefficientExact CoefficientBounded Boundary Projection :=
  Adjunction.ofIsLeftAdjoint (coefficientEnhancedQ X CoefficientExact CoefficientBounded Boundary Projection)

abbrev boundedCoefficientTensor : BoundedModules (KY X) (KY X) ⥤
    DerivedCategory (Bimod (RY n X Real First Graph) (KY X)) ⥤
      DerivedCategory (Bimod (RY n X Real First Graph) (KY X)) :=
  (IsBoundedDerived (Bimod (KY X) (KY X))).ι ⋙ kernelCoefficientTensor n X Real First Graph

variable [∀ H : BoundedModules (KY X) (KY X),
    ((boundedCoefficientTensor n X Real First Graph).obj H).IsLeftAdjoint]
  [(originalOrdinaryBetaPull n X Real First Graph Geometry N Normalize BetaExact).IsLeftAdjoint]
  (M : DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
    (analyticDifferentialRing n X)))
  (BoundedSolution : IsBoundedDerived (Bimod (KY X) (KY X))
    ((solutionsWithKernel n X Real First Graph Geometry N Normalize BetaExact
      Representatives Kernel).obj (Opposite.op M)))

def sourceSolution : BoundedModules (KY X) (KY X) :=
  ⟨(solutionsWithKernel n X Real First Graph Geometry N Normalize BetaExact
    Representatives Kernel).obj (Opposite.op M), BoundedSolution⟩

/-- The computed reconstruction target uses the actual ambient tensor-Hom and beta-pi right adjoints. -/
def originalReconstructionTarget :
    DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)) :=
    (originalOrdinaryBetaPull n X Real First Graph Geometry N Normalize BetaExact).rightAdjoint.obj
      ((((boundedCoefficientTensor n X Real First Graph).obj
        ((coefficientLeftRepresentative X CoefficientExact CoefficientBounded Boundary Projection).obj
          ((coefficientEnhancedQ X CoefficientExact CoefficientBounded Boundary Projection).obj
            (sourceSolution n X Real First Graph Geometry N Normalize BetaExact Representatives Kernel M
              BoundedSolution)))).rightAdjoint).obj
                (rightLocalKernel n X Real First Graph Geometry Representatives Kernel))

/-- The exact ordinary D-module reconstruction map from the native evaluation and both source mates. -/
def originalReconstructionMap : M ⟶
    originalReconstructionTarget n X Real First Graph Geometry N Normalize BetaExact Representatives
      Kernel CoefficientExact CoefficientBounded Boundary Projection M BoundedSolution :=
  MathlibExt.CategoryTheory.NativeRingedReconstructionMaps.reconstructionMap
    (coefficientEnhancedQ X CoefficientExact CoefficientBounded Boundary Projection)
    (coefficientLeftRepresentative X CoefficientExact CoefficientBounded Boundary Projection)
    (coefficientLeftAdjunction X CoefficientExact CoefficientBounded Boundary Projection)
    (boundedCoefficientTensor n X Real First Graph)
    (originalOrdinaryBetaPull n X Real First Graph Geometry N Normalize BetaExact)
    (originalOrdinaryBetaPull n X Real First Graph Geometry N Normalize BetaExact).rightAdjoint
    (Adjunction.ofIsLeftAdjoint (originalOrdinaryBetaPull n X Real First Graph Geometry N Normalize BetaExact))
    M (sourceSolution n X Real First Graph Geometry N Normalize BetaExact Representatives Kernel M BoundedSolution)
    (rightLocalKernel n X Real First Graph Geometry Representatives Kernel)
    (kernelEvaluation n X Real First Graph Geometry N Normalize BetaExact Representatives Kernel M)

end MathlibExt.AlgebraicGeometry.NativeKernelReconstructionModels
