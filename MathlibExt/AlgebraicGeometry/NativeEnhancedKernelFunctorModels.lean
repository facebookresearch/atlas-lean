/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeEnhancedModuleGeometry
public import MathlibExt.AlgebraicGeometry.NativeBetaModuleDerivedModels
public import MathlibExt.AlgebraicGeometry.NativeOmegaTransferModels
public import MathlibExt.CategoryTheory.NativeEnhancedDModuleExpressions

/-!
# Source kernel de Rham/solution operations on the actual ringed geometry

The ordinary input functor is actual beta followed by the original
product/real-graph inverse images. Top-form transfer is the actual native
Omega tensor regular-D source mapped by those same inverse images.
The endpoint is the native right representative of the fixed ringed
enhanced quotient. De Rham is covariant balanced D-tensor; solutions are
contravariant module Hom. Instantiation with the computed O^E source is
the enhanced DR/Sol of Definition9.1.1.

Source: DK1311.2374v2 Definitions8.2.1,9.1.1;
Mathlib56a005 native beta, inverse image, top forms, Hom/tensor and Q, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeEnhancedKernelFunctorModels

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves NativeIndDifferentialContexts NativeIndModuleInverseModels
open NativeEnhancedModuleGeometry NativeBetaModuleDerivedModels NativeOmegaTransferModels
open ProjectiveExponentialSectionModels ProductDifferentialOperatorModels
open HolomorphicCotangentModuleModels BorderedIndDerivedModels EnhancedIndQuotientModels
open MathlibExt.CategoryTheory.NativeRingedAdjointImageModels
open MathlibExt.CategoryTheory.NativeMonoidalBimoduleMapping
open MathlibExt.CategoryTheory.NativeOppositeBimoduleModels
open MathlibExt.CategoryTheory.NativeDerivedBimoduleCalculus
open MathlibExt.CategoryTheory.NativeEnhancedBimoduleQuotients
open MathlibExt.CategoryTheory.NativeEnhancedDModuleExpressions
open scoped Manifold ContDiff

variable [∀ Z : TopCat.{0}, HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
  (n : ℕ) (X : Type) [TopologicalSpace X]
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

local instance kernelFirstBraided : (originalInverse (xProjection X) First).Braided := First.braided
local instance kernelGraphBraided :
    (originalInverse (realGraphInclusion (TopCat.of X) Real) Graph).Braided := Graph.braided

abbrev RY := RealInverseDX n X Real First Graph
abbrev RYop := inverseRing (realGraphInclusion (TopCat.of X) Real) Graph
  (inverseRing (xProjection X) First (betaRing (TopCat.of X) (analyticOppositeDifferentialRing n X)))
abbrev KY := Mon.trivial (IndSheaf ℂ (enhancedSpace (TopCat.of X)).ambient)

local instance kernelModulePreadditive (Z : TopCat.{0})
    [HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
    [CompactSheafSource ℂ Z] [IndSpaceSource Z] (R S : Mon (IndSheaf ℂ Z)) :
    Preadditive (Bimod R S) := Abelian.toPreadditive
local instance kernelOrdinaryPreadditive :
    Preadditive (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)) := Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

variable (N : OrdinaryBetaModuleSource (TopCat.of X) (analyticDifferentialRing n X))
  (Normalize : BetaUnitNormalizationSource (TopCat.of X) (analyticDifferentialRing n X))
  [(betaUnitModules (TopCat.of X) (analyticDifferentialRing n X) N Normalize).Additive]
  (BetaExact : ExactImageSource
    (betaUnitModules (TopCat.of X) (analyticDifferentialRing n X) N Normalize))

def originalOrdinaryBetaPull :
    DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)) ⥤ DerivedCategory (Bimod (RY n X Real First Graph) (KY X)) :=
  letI := Geometry.firstAdditive
  letI := Geometry.graphAdditive
  derivedBetaModules (TopCat.of X) (analyticDifferentialRing n X) N Normalize BetaExact ⋙
    derivedIndModuleInverse (xProjection X) First (BaseDX n X)
      Geometry.firstImage Geometry.firstExact ⋙
    derivedIndModuleInverse (realGraphInclusion (TopCat.of X) Real) Graph
      (ProductInverseDX n X First) Geometry.graphImage Geometry.graphExact

variable (Representatives : ModuleRepresentativeSource (RY n X Real First Graph) (KY X)
    (nativeBoundaryImage n X Real First Graph Geometry) (nativeBaseInverse n X Real First Graph Geometry))
  (Kernel : NativeEnhancedDModules n X Real First Graph Geometry)

def rightLocalKernel : DerivedCategory (Bimod (RY n X Real First Graph) (KY X)) :=
  ((moduleRightRepresentative (RY n X Real First Graph) (KY X)
    (nativeBoundaryImage n X Real First Graph Geometry) (nativeBaseInverse n X Real First Graph Geometry)
      Representatives).obj Kernel).obj

variable [HolomorphicCoefficientSheaves.SheafCondition
    (TemperedDistributionSectionModels.ComplexCoordinates n) X]
  [CotangentSectionCalculus (n := n) (M := X)] [CotangentSheafCondition (n := n) (M := X)]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
  (Omega : OmegaTransferSource n X)
  (OmegaFirst : BimoduleMappingSource (originalInverse (xProjection X) First)
    (betaRing (TopCat.of X) (analyticOppositeDifferentialRing n X)) (BaseDX n X))
  (OmegaGraph : BimoduleMappingSource (originalInverse (realGraphInclusion (TopCat.of X) Real) Graph)
    (inverseRing (xProjection X) First (betaRing (TopCat.of X) (analyticOppositeDifferentialRing n X)))
    (ProductInverseDX n X First))

def originalOmegaTransfer : DerivedCategory (Bimod (RYop n X Real First Graph) (RY n X Real First Graph)) :=
  (DerivedCategory.singleFunctor (Bimod (RYop n X Real First Graph) (RY n X Real First Graph)) 0).obj
    (OmegaGraph.functor.obj (OmegaFirst.functor.obj (nativeOmegaTransfer n X Omega)))

variable (RBack : OppositeMonoidSource (RYop n X Real First Graph) (RY n X Real First Graph))
  (UnitOpp : OppositeMonoidSource (KY X) (KY X))
  (RightView : OppositeBimoduleSource (RYop n X Real First Graph) (KY X)
    (RY n X Real First Graph) (KY X) RBack UnitOpp)
  [RightView.functor.Additive] (RightExact : ExactImageSource RightView.functor)
  [TensorDerivationSource (RYop n X Real First Graph) (RY n X Real First Graph) (KY X)]

def omegaKernelRaw : DerivedCategory (Bimod (KY X) (RY n X Real First Graph)) :=
  enhancedOmegaRaw (RY n X Real First Graph) (RYop n X Real First Graph) (KY X)
    (originalOmegaTransfer n X Real First Graph Omega OmegaFirst OmegaGraph)
    (derivedExactImage RightView.functor RightExact)
      (rightLocalKernel n X Real First Graph Geometry Representatives Kernel)

variable [TensorDerivationSource (KY X) (RY n X Real First Graph) (KY X)]

/-- Covariant D-tensor operation on the fixed source kernel and actual beta-pulled input. -/
def deRhamWithKernel :
    DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)) ⥤ DerivedCategory (Bimod (KY X) (KY X)) :=
  enhancedDRRaw (RY n X Real First Graph) (KY X)
    (originalOrdinaryBetaPull n X Real First Graph Geometry N Normalize BetaExact)
    (omegaKernelRaw n X Real First Graph Geometry Representatives Kernel Omega OmegaFirst OmegaGraph
      RBack UnitOpp RightView RightExact)

variable (ROpp : OppositeMonoidSource (RY n X Real First Graph) (RYop n X Real First Graph))
  (SolView : OppositeBimoduleSource (RY n X Real First Graph) (KY X)
    (RYop n X Real First Graph) (KY X) ROpp UnitOpp)
  [SolView.functor.Additive] (SolExact : ExactImageSource SolView.functor)
  [TensorDerivationSource (KY X) (KY X) (RYop n X Real First Graph)]
  [TensorHomSource (KY X) (KY X) (RYop n X Real First Graph)]

/-- Contravariant native module Hom into the actual right-local source kernel. -/
def solutionsWithKernelOpposite :
    (DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)))ᵒᵖ ⥤ DerivedCategory (Bimod (KY X) (KY X)) :=
  enhancedSolRaw (RYop n X Real First Graph) (KY X)
    (originalOrdinaryBetaPull n X Real First Graph Geometry N Normalize BetaExact ⋙
      derivedExactImage SolView.functor SolExact)
    ((derivedExactImage SolView.functor SolExact).obj
      (rightLocalKernel n X Real First Graph Geometry Representatives Kernel))

variable [LeftTensorDerivationSource (RY n X Real First Graph) (KY X) (KY X)]
  [LeftTensorHomSource (RY n X Real First Graph) (KY X) (KY X)]

/-- Direct left-D module Hom, contravariant in the original beta-pulled ordinary module. -/
def solutionsWithKernel :
    (DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)))ᵒᵖ ⥤ DerivedCategory (Bimod (KY X) (KY X)) :=
  (originalOrdinaryBetaPull n X Real First Graph Geometry N Normalize BetaExact).op ⋙
    homLeftDerived (RY n X Real First Graph) (KY X) (KY X) ⋙
      (_root_.CategoryTheory.evaluation (DerivedCategory (Bimod (RY n X Real First Graph) (KY X)))
        (DerivedCategory (Bimod (KY X) (KY X)))).obj
          (rightLocalKernel n X Real First Graph Geometry Representatives Kernel)

/-- Original native evaluation in the endpoint left-D module category. -/
def kernelEvaluation (M : DerivedCategory
    (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X) (analyticDifferentialRing n X))) :
    ((tensorDerivedLeft (RY n X Real First Graph) (KY X) (KY X)).obj
      ((originalOrdinaryBetaPull n X Real First Graph Geometry N Normalize BetaExact).obj M)).obj
        ((solutionsWithKernel n X Real First Graph Geometry N Normalize BetaExact
          Representatives Kernel).obj (Opposite.op M)) ⟶
            rightLocalKernel n X Real First Graph Geometry Representatives Kernel :=
  evaluationLeft (RY n X Real First Graph) (KY X) (KY X)
    ((originalOrdinaryBetaPull n X Real First Graph Geometry N Normalize BetaExact).obj M)
    (rightLocalKernel n X Real First Graph Geometry Representatives Kernel)

/-- The actual ambient coefficient tensor retaining the D action, with its original parameter order flipped. -/
abbrev kernelCoefficientTensor : DerivedCategory (Bimod (KY X) (KY X)) ⥤
    DerivedCategory (Bimod (RY n X Real First Graph) (KY X)) ⥤
      DerivedCategory (Bimod (RY n X Real First Graph) (KY X)) :=
  (tensorDerivedLeft (RY n X Real First Graph) (KY X) (KY X)).flip

end MathlibExt.AlgebraicGeometry.NativeEnhancedKernelFunctorModels
