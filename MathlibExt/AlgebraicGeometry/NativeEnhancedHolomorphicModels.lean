/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeProductModuleViews
public import MathlibExt.AlgebraicGeometry.NativeTemperedOPackets
public import MathlibExt.AlgebraicGeometry.NativeProjectiveExponentialPackets
public import MathlibExt.AlgebraicGeometry.NativeEnhancedModuleGeometry
public import MathlibExt.CategoryTheory.NativeEnhancedDModuleExpressions
public import MathlibExt.AlgebraicGeometry.NativeEnhancedKernelFunctorModels
public import MathlibExt.AlgebraicGeometry.NativeKernelReconstructionModels
public import MathlibExt.AlgebraicGeometry.HolonomicCharacteristicSupportModels
public import MathlibExt.AlgebraicGeometry.RegularHolonomicModels

/-!
# Actual O_X^E from the original product tau-Hom and ringed real graph

The product O^t is the source-qualified actual Dbar-Hom object. All full
X/P operator views come from the original slice-normalized embeddings.
The exp(tau) and r(exp(-tau)) inputs retain the native P modules and
Omega_P tensor. i! is the actual ringed graph proper image's native right
adjoint. The Hom realization uses [2], and the balanced right realization
uses [1]. The final enhanced object passes through the exact source
closed-boundary/pi-image module quotient.

Source: DK1311.2374v2 Definition8.2.1 and Theorem8.2.2;
Mathlib56a005 native beta, module Hom/tensor, i! and Q, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeEnhancedHolomorphicModels

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves NativeIndDifferentialContexts
open ProjectiveExponentialSectionModels ProductDifferentialOperatorModels NativeProductModuleViews
open NativeBetaInverseCompatibility NativeOrdinaryDifferentialRepresentations PulledBetaRingModels
open NativeIndModuleInverseModels NativeRingedIndImageModels NativeEnhancedModuleGeometry
open NativeTemperedOPackets NativeProjectiveExponentialPackets HolomorphicCotangentModuleModels
open BoundedIndOperationSources EnhancedIndQuotientModels BorderedIndDerivedModels EnhancedConvolutionModels
open MathlibExt.CategoryTheory.NativeRingedAdjointImageModels
open MathlibExt.CategoryTheory.NativeOppositeBimoduleModels
open MathlibExt.CategoryTheory.NativeDerivedBimoduleCalculus
open MathlibExt.CategoryTheory.NativeBoundedBimoduleModels
open scoped Manifold ContDiff

variable [∀ Z : TopCat.{0}, HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
  (n : ℕ) (X : Type) [TopologicalSpace X]
  [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) X]
  [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ X]
  [ProjectiveComplexSource] [ProductComplexSource n X]
  [HasSheafify (Opens.grothendieckTopology X) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology ProjectiveLine) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology (X × ProjectiveLine)) RingCat.{0}]
  [HolomorphicCoefficientSheaves.SheafCondition ProjectiveCoordinates ProjectiveLine]
  [CotangentSectionCalculus (n := 1) (M := ProjectiveLine)]
  [CotangentSheafCondition (n := 1) (M := ProjectiveLine)]
  [HasSheafify (Opens.grothendieckTopology ProjectiveLine) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology ProjectiveLine).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [CompactSheafSource ℂ (TopCat.of X)] [IndSpaceSource (TopCat.of X)]
  [CompactSheafSource ℂ (TopCat.of ProjectiveLine)] [IndSpaceSource (TopCat.of ProjectiveLine)]
  [CompactSheafSource ℂ (ProductSpace X)] [IndSpaceSource (ProductSpace X)]
  [CompactSheafSource ℂ (enhancedSpace (TopCat.of X)).ambient]
  [IndSpaceSource (enhancedSpace (TopCat.of X)).ambient]
  [CompactSheafSource ℂ (boundarySpace (enhancedSpace (TopCat.of X)))]
  [IndSpaceSource (boundarySpace (enhancedSpace (TopCat.of X)))]
  [DifferentialBetaSource X (analyticCoefficients n X)]
  [OppositeDifferentialBetaSource X (analyticCoefficients n X)]
  [DifferentialBetaSource ProjectiveLine (analyticCoefficients 1 ProjectiveLine)]
  [OppositeDifferentialBetaSource ProjectiveLine (analyticCoefficients 1 ProjectiveLine)]
  [DifferentialBetaSource (X × ProjectiveLine) (analyticCoefficients (n + 1) (X × ProjectiveLine))]
  [DifferentialBetaSource (X × ProjectiveLine)
    (analyticConjugateCoefficients (n + 1) (X × ProjectiveLine))]
  [OppositeDifferentialBetaSource (X × ProjectiveLine)
    (analyticConjugateCoefficients (n + 1) (X × ProjectiveLine))]
  (IX : InverseMonoidalSource (xProjection X)) (IP : InverseMonoidalSource (pProjection X))
  [OrdinaryInverseMonoidalSource (xProjection X)] [OrdinaryInverseMonoidalSource (pProjection X)]
  [PulledBetaRingSource (xProjection X) (XRing n X)] [PulledBetaRingSource (pProjection X) PRing]
  (NX : BetaInverseNaturalSource (xProjection X) IX)
  (NP : BetaInverseNaturalSource (pProjection X) IP)
  (PX : OrdinaryRingPullbackSource (xProjection X) (XRing n X))
  (PP : OrdinaryRingPullbackSource (pProjection X) PRing)
  (Structure : StructureModuleSource (X × ProjectiveLine)
    (analyticCoefficients (n + 1) (X × ProjectiveLine)))
  (Operators : ProductOperatorSource n X Structure)
  (MX : OrdinaryRingMapSource (ProductSpace X) (ProjectedXRing n X) (FullProductRing n X) Operators.xMap)
  (MP : OrdinaryRingMapSource (ProductSpace X) (ProjectedPRing X) (FullProductRing n X) Operators.pMap)
  (V : ProductModuleViewSource n X IX IP NX NP PX PP Structure Operators MX MP)
  (Ot : TemperedOData (n + 1) (X × ProjectiveLine))

local instance enhancedOInputPreadditive (Z : TopCat.{0})
    [HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
    [CompactSheafSource ℂ Z] [IndSpaceSource Z] (R S : Mon (IndSheaf ℂ Z)) :
    Preadditive (Bimod R S) := Abelian.toPreadditive
local instance enhancedOIndPreadditive (Z : TopCat.{0}) [CompactSheafSource ℂ Z] :
    Preadditive (IndSheaf ℂ Z) := Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

variable [V.homView.functor.Additive] [V.tensorView.functor.Additive]
  (HE : ExactImageSource V.homView.functor) (TE : ExactImageSource V.tensorView.functor)

def productHomO : DerivedCategory (Bimod (InverseDX n X IX) (InverseDPop X IP)) :=
  (derivedExactImage V.homView.functor HE).obj (temperedOWithUnit (n + 1) (X × ProjectiveLine) Ot)

def productTensorO : DerivedCategory (Bimod (InverseDP X IP) (InverseDXop n X IX)) :=
  (derivedExactImage V.tensorView.functor TE).obj (temperedOWithUnit (n + 1) (X × ProjectiveLine) Ot)

variable (Exp : ProjectiveExponentialData)
  (Plus : LeftUnitIndModuleInverseSource (pProjection X) IP DPop)
  (Minus : LeftUnitIndModuleInverseSource (pProjection X) IP DP)
  [TensorDerivationSource (InverseDX n X IX) (Mon.trivial (IndSheaf ℂ (ProductSpace X)))
    (InverseDPop X IP)]
  [TensorHomSource (InverseDX n X IX) (Mon.trivial (IndSheaf ℂ (ProductSpace X)))
    (InverseDPop X IP)]

def actualProductTauHom :
    DerivedCategory (Bimod (InverseDX n X IX) (Mon.trivial (IndSheaf ℂ (ProductSpace X)))) :=
  MathlibExt.CategoryTheory.NativeEnhancedDModuleExpressions.productTauHom
    (InverseDX n X IX) (Mon.trivial (IndSheaf ℂ (ProductSpace X))) (InverseDPop X IP)
      (projectedPlus Exp (ProductSpace X) (pProjection X) IP Plus)
      (productHomO n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE)

variable [TensorDerivationSource (Mon.trivial (IndSheaf ℂ (ProductSpace X)))
    (InverseDP X IP) (InverseDXop n X IX)]
  (XBack : OppositeMonoidSource (InverseDXop n X IX) (InverseDX n X IX))
  (UnitOpp : OppositeMonoidSource (Mon.trivial (IndSheaf ℂ (ProductSpace X)))
    (Mon.trivial (IndSheaf ℂ (ProductSpace X))))
  (Back : OppositeBimoduleSource (Mon.trivial (IndSheaf ℂ (ProductSpace X)))
    (InverseDXop n X IX) (Mon.trivial (IndSheaf ℂ (ProductSpace X))) (InverseDX n X IX) UnitOpp XBack)
  [Back.functor.Additive] (BE : ExactImageSource Back.functor)

def actualProductRightTensor :
    DerivedCategory (Bimod (InverseDX n X IX) (Mon.trivial (IndSheaf ℂ (ProductSpace X)))) :=
  (derivedExactImage Back.functor BE).obj
    (((tensorDerived (Mon.trivial (IndSheaf ℂ (ProductSpace X))) (InverseDP X IP)
      (InverseDXop n X IX)).obj
        (productTensorO n X IX IP NX NP PX PP Structure Operators MX MP V Ot TE)).obj
          (projectedRightMinus Exp (ProductSpace X) (pProjection X) IP Minus))

variable (Real : RealProjectiveMapSource)
  (Graph : InverseMonoidalSource (realGraphInclusion (TopCat.of X) Real))
  (Proper : ProperSource ℂ (realGraphInclusion (TopCat.of X) Real))
  (Adj : originalInverse (realGraphInclusion (TopCat.of X) Real) Graph ⊣
    originalProper (realGraphInclusion (TopCat.of X) Real) Proper)
  (Image : RingedIndImageSource (realGraphInclusion (TopCat.of X) Real) Graph Proper Adj
    (ProductInverseDX n X IX))
  [(originalRingedProper (realGraphInclusion (TopCat.of X) Real) Graph Proper Adj
    (ProductInverseDX n X IX) Image).Additive]
  (Derivation : RightDerivationSource
    (originalRingedProper (realGraphInclusion (TopCat.of X) Real) Graph Proper Adj
      (ProductInverseDX n X IX) Image))
  [(derivedRingedProper (realGraphInclusion (TopCat.of X) Real) Graph Proper Adj
    (ProductInverseDX n X IX) Image Derivation).IsLeftAdjoint]

def actualEnhancedORaw :
    DerivedCategory (Bimod (RealInverseDX n X Real IX Graph)
      (Mon.trivial (IndSheaf ℂ (enhancedSpace (TopCat.of X)).ambient))) :=
  MathlibExt.CategoryTheory.NativeEnhancedDModuleExpressions.enhancedORaw
    (RealInverseDX n X Real IX Graph) (Mon.trivial (IndSheaf ℂ (enhancedSpace (TopCat.of X)).ambient))
      ((ringedExceptional (realGraphInclusion (TopCat.of X) Real) Graph Proper Adj
        (ProductInverseDX n X IX) Image Derivation).obj
          (actualProductTauHom n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus))

def actualEnhancedORightRaw :
    DerivedCategory (Bimod (RealInverseDX n X Real IX Graph)
      (Mon.trivial (IndSheaf ℂ (enhancedSpace (TopCat.of X)).ambient))) :=
  MathlibExt.CategoryTheory.NativeEnhancedDModuleExpressions.enhancedORightRaw
    (RealInverseDX n X Real IX Graph) (Mon.trivial (IndSheaf ℂ (enhancedSpace (TopCat.of X)).ambient))
      ((ringedExceptional (realGraphInclusion (TopCat.of X) Real) Graph Proper Adj
        (ProductInverseDX n X IX) Image Derivation).obj
          (actualProductRightTensor n X IX IP NX NP PX PP Structure Operators MX MP V Ot TE
            Exp Minus XBack UnitOpp Back BE))

variable (Geometry : EnhancedModuleGeometrySource n X Real IX Graph)
  (BoundedO : IsBoundedDerived
    (Bimod (RealInverseDX n X Real IX Graph)
      (Mon.trivial (IndSheaf ℂ (enhancedSpace (TopCat.of X)).ambient)))
    (actualEnhancedORaw n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
      Real Graph Proper Adj Image Derivation))

/-- The source enhanced O object is the exact module quotient of the computed Hom [2] representative. -/
def actualEnhancedO : NativeEnhancedDModules n X Real IX Graph Geometry :=
  (nativeModuleQ n X Real IX Graph Geometry).obj
    ⟨actualEnhancedORaw n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
      Real Graph Proper Adj Image Derivation, BoundedO⟩

/-- The full right-P balanced [1] construction in the same actual enhanced D-module quotient. -/
def actualEnhancedORight (RightBounded : IsBoundedDerived
    (Bimod (RealInverseDX n X Real IX Graph)
      (Mon.trivial (IndSheaf ℂ (enhancedSpace (TopCat.of X)).ambient)))
    (actualEnhancedORightRaw n X IX IP NX NP PX PP Structure Operators MX MP V Ot TE
      Exp Minus XBack UnitOpp Back BE Real Graph Proper Adj Image Derivation)) :
    NativeEnhancedDModules n X Real IX Graph Geometry :=
  (nativeModuleQ n X Real IX Graph Geometry).obj
    ⟨actualEnhancedORightRaw n X IX IP NX NP PX PP Structure Operators MX MP V Ot TE
      Exp Minus XBack UnitOpp Back BE Real Graph Proper Adj Image Derivation, RightBounded⟩

open NativeEnhancedKernelFunctorModels NativeOmegaTransferModels NativeBetaModuleDerivedModels
open MathlibExt.CategoryTheory.NativeMonoidalBimoduleMapping
open MathlibExt.CategoryTheory.NativeEnhancedBimoduleQuotients

local instance sourceFirstBraided : (originalInverse (xProjection X) IX).Braided := IX.braided
local instance sourceGraphBraided :
    (originalInverse (realGraphInclusion (TopCat.of X) Real) Graph).Braided := Graph.braided

variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{0}]
  (Ordinary : OrdinaryBetaModuleSource (TopCat.of X) (analyticDifferentialRing n X))
  (Normalize : BetaUnitNormalizationSource (TopCat.of X) (analyticDifferentialRing n X))
  [(betaUnitModules (TopCat.of X) (analyticDifferentialRing n X) Ordinary Normalize).Additive]
  (BetaExact : ExactImageSource
    (betaUnitModules (TopCat.of X) (analyticDifferentialRing n X) Ordinary Normalize))
  (Representatives : ModuleRepresentativeSource (RealInverseDX n X Real IX Graph)
    (Mon.trivial (IndSheaf ℂ (enhancedSpace (TopCat.of X)).ambient))
      (nativeBoundaryImage n X Real IX Graph Geometry) (nativeBaseInverse n X Real IX Graph Geometry))

variable [HolomorphicCoefficientSheaves.SheafCondition
    (TemperedDistributionSectionModels.ComplexCoordinates n) X]
  [CotangentSectionCalculus (n := n) (M := X)] [CotangentSheafCondition (n := n) (M := X)]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
  (Omega : OmegaTransferSource n X)
  (OmegaFirst : BimoduleMappingSource (originalInverse (xProjection X) IX)
    (betaRing (TopCat.of X) (analyticOppositeDifferentialRing n X)) (BaseDX n X))
  (OmegaGraph : BimoduleMappingSource (originalInverse (realGraphInclusion (TopCat.of X) Real) Graph)
    (inverseRing (xProjection X) IX (betaRing (TopCat.of X) (analyticOppositeDifferentialRing n X)))
    (ProductInverseDX n X IX))
  (RBack : OppositeMonoidSource (RYop n X Real IX Graph) (RealInverseDX n X Real IX Graph))
  (UnitOppY : OppositeMonoidSource (KY X) (KY X))
  (RightView : OppositeBimoduleSource (RYop n X Real IX Graph) (KY X)
    (RealInverseDX n X Real IX Graph) (KY X)
      RBack UnitOppY)
  [RightView.functor.Additive] (RightExact : ExactImageSource RightView.functor)
  [TensorDerivationSource (RYop n X Real IX Graph) (RealInverseDX n X Real IX Graph) (KY X)]
  [TensorDerivationSource (KY X) (RealInverseDX n X Real IX Graph) (KY X)]

/-- Definition9.1.1 DR built from the actual source O^E, actual Omega transfer and beta-pulled module. -/
def actualEnhancedDRRaw :
    DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)) ⥤
        DerivedCategory (Bimod (KY X) (KY X)) :=
  deRhamWithKernel n X Real IX Graph Geometry Ordinary Normalize BetaExact Representatives
    (actualEnhancedO n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
      Real Graph Proper Adj Image Derivation Geometry BoundedO)
    Omega OmegaFirst OmegaGraph RBack UnitOppY RightView RightExact

variable [LeftTensorDerivationSource (RealInverseDX n X Real IX Graph) (KY X) (KY X)]
  [LeftTensorHomSource (RealInverseDX n X Real IX Graph) (KY X) (KY X)]

/-- Definition9.1.1 Sol is the actual contravariant native left-D Hom into R_D^E of this source O^E. -/
def actualEnhancedSolRaw :
    (DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)))ᵒᵖ ⥤
        DerivedCategory (Bimod (KY X) (KY X)) :=
  solutionsWithKernel n X Real IX Graph Geometry Ordinary Normalize BetaExact Representatives
    (actualEnhancedO n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
      Real Graph Proper Adj Image Derivation Geometry BoundedO)

open NativeKernelReconstructionModels

variable [T2Space X] [(Bimod.forget (B := KY X) (KY X)).Additive]
  (CoefficientExact : ExactCoefficientSource (KY X) (KY X))
  (CoefficientBounded : BoundedCoefficientSource (KY X) (KY X) CoefficientExact)
  (Boundary : ProperSource ℂ (boundaryInclusion (enhancedSpace (TopCat.of X))))
  (Projection : InverseSource ℂ (baseProjection (TopCat.of X)))

abbrev sourceDRCoefficients :
    DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)) ⥤ IndDerived ℂ (enhancedSpace (TopCat.of X)).ambient :=
  actualEnhancedDRRaw n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
    Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
      Representatives Omega OmegaFirst OmegaGraph RBack UnitOppY RightView RightExact ⋙
        derivedCoefficients (KY X) (KY X) CoefficientExact

abbrev sourceSolCoefficients :
    (DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)))ᵒᵖ ⥤ IndDerived ℂ (enhancedSpace (TopCat.of X)).ambient :=
  actualEnhancedSolRaw n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
    Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact Representatives ⋙
      derivedCoefficients (KY X) (KY X) CoefficientExact

variable
  (DRBounded : ∀ M : (IsBoundedDerived (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
    (analyticDifferentialRing n X))).FullSubcategory,
    IsBounded ℂ (enhancedSpace (TopCat.of X)).ambient
      ((sourceDRCoefficients n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
        Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
          Representatives Omega OmegaFirst OmegaGraph RBack UnitOppY RightView RightExact CoefficientExact).obj M.obj))
  (SolBounded : ∀ M : (IsBoundedDerived (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
    (analyticDifferentialRing n X))).FullSubcategory,
    IsBounded ℂ (enhancedSpace (TopCat.of X)).ambient
      ((sourceSolCoefficients n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
        Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
          Representatives CoefficientExact).obj (Opposite.op M.obj)))

/-- Actual covariant enhanced DR on bounded ordinary D-modules. -/
def actualEnhancedDR :
    (IsBoundedDerived (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X))).FullSubcategory ⥤
        EnhancedCategory ℂ (TopCat.of X) Boundary Projection :=
  (IsBounded ℂ (enhancedSpace (TopCat.of X)).ambient).lift
    ((IsBoundedDerived (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X))).ι ⋙
        sourceDRCoefficients n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
          Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
            Representatives Omega OmegaFirst OmegaGraph RBack UnitOppY RightView RightExact
              CoefficientExact) DRBounded ⋙
    enhancedSourceProjection ℂ (TopCat.of X) Boundary Projection

/-- Actual contravariant enhanced Sol on bounded ordinary D-modules. -/
def actualEnhancedSol :
    ((IsBoundedDerived (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X))).FullSubcategory)ᵒᵖ ⥤
        EnhancedCategory ℂ (TopCat.of X) Boundary Projection :=
  (IsBounded ℂ (enhancedSpace (TopCat.of X)).ambient).lift
    ((IsBoundedDerived (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X))).ι.op ⋙
        sourceSolCoefficients n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
          Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
            Representatives CoefficientExact) (fun M => SolBounded M.unop) ⋙
    enhancedSourceProjection ℂ (TopCat.of X) Boundary Projection

variable [∀ U : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{0}]
  [∀ U : Opens X,
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ (U : Opens X) (W : Over U), HasWeakSheafify
    (((Opens.grothendieckTopology X).over U).over W) AddCommGrpCat.{0}]
  [∀ (U : Opens X) (W : Over U),
    (((Opens.grothendieckTopology X).over U).over W).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- Actual enhanced DR restricted by original D-module cohomological holonomicity. -/
def actualHolonomicEnhancedDR :=
  (HolonomicCharacteristicSupportModels.IsBoundedHolonomic n X).ιOfLE
    (show HolonomicCharacteristicSupportModels.IsBoundedHolonomic n X ≤
      IsBoundedDerived (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
        (analyticDifferentialRing n X)) from fun _ h => h.1) ⋙
  actualEnhancedDR n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
    Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
      Representatives Omega OmegaFirst OmegaGraph RBack UnitOppY RightView RightExact
        CoefficientExact Boundary Projection DRBounded

/-- The same holonomic restriction with the original contravariant Sol maps. -/
def actualHolonomicEnhancedSol :=
  ((HolonomicCharacteristicSupportModels.IsBoundedHolonomic n X).ιOfLE
    (show HolonomicCharacteristicSupportModels.IsBoundedHolonomic n X ≤
      IsBoundedDerived (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
        (analyticDifferentialRing n X)) from fun _ h => h.1)).op ⋙
  actualEnhancedSol n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
    Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
      Representatives CoefficientExact Boundary Projection SolBounded

/-- Actual enhanced DR on the native bounded regular-holonomic full subcategory. -/
def actualRegularHolonomicEnhancedDR :=
  RegularHolonomicModels.regularHolonomicInclusion n X ⋙
    actualHolonomicEnhancedDR n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
      Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
        Representatives Omega OmegaFirst OmegaGraph RBack UnitOppY RightView RightExact
          CoefficientExact Boundary Projection DRBounded

/-- The same native regular restriction, retaining contravariant solution maps. -/
def actualRegularHolonomicEnhancedSol :=
  (RegularHolonomicModels.regularHolonomicInclusion n X).op ⋙
    actualHolonomicEnhancedSol n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
      Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
        Representatives CoefficientExact Boundary Projection SolBounded

variable
  [quotientLeftAdjoint :
    (coefficientEnhancedQ X CoefficientExact CoefficientBounded Boundary Projection).IsRightAdjoint]
  [tensorClosed : ∀ H : BoundedModules (KY X) (KY X),
    ((boundedCoefficientTensor n X Real IX Graph).obj H).IsLeftAdjoint]
  [betaPullRightAdjoint :
    (originalOrdinaryBetaPull n X Real IX Graph Geometry Ordinary Normalize BetaExact).IsLeftAdjoint]
  (M : DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
    (analyticDifferentialRing n X)))
  (BoundedSolution : IsBoundedDerived (Bimod (KY X) (KY X))
    ((actualEnhancedSolRaw n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
      Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
        Representatives).obj (Opposite.op M)))

variable [(Bimod.forget (B := KY X) (RealInverseDX n X Real IX Graph)).Additive]
  (OCoefficientExact : ExactCoefficientSource (RealInverseDX n X Real IX Graph) (KY X))
  (OCoefficientBounded : IsBounded ℂ (enhancedSpace (TopCat.of X)).ambient
    ((derivedCoefficients (RealInverseDX n X Real IX Graph) (KY X) OCoefficientExact).obj
      (actualEnhancedORaw n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
        Real Graph Proper Adj Image Derivation)))

/-- The actual source O^E in enhanced coefficient sheaves, with all carrier maps fixed by forgetting. -/
def actualEnhancedOCoefficients : EnhancedCategory ℂ (TopCat.of X) Boundary Projection :=
  (enhancedSourceProjection ℂ (TopCat.of X) Boundary Projection).obj
    ⟨(derivedCoefficients (RealInverseDX n X Real IX Graph) (KY X) OCoefficientExact).obj
      (actualEnhancedORaw n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
        Real Graph Proper Adj Image Derivation), OCoefficientBounded⟩

variable (OAllBounded : BoundedCoefficientSource
    (RealInverseDX n X Real IX Graph) (KY X) OCoefficientExact)
  (OFactor : ModuleCoefficientQuotientSource (RealInverseDX n X Real IX Graph) (KY X)
    (nativeBoundaryImage n X Real IX Graph Geometry) (nativeBaseInverse n X Real IX Graph Geometry)
    (moduleCoefficientQuotientInput n X Real IX Graph Boundary Projection OCoefficientExact OAllBounded))

/-- Native factorization identifies the coefficient image of the actual enhanced O with its original raw quotient. -/
def actualEnhancedOCoefficientComparison :
    (moduleCoefficientFunctor n X Real IX Graph Geometry Boundary Projection
      OCoefficientExact OAllBounded OFactor).obj
        (actualEnhancedO n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
          Real Graph Proper Adj Image Derivation Geometry BoundedO) ≅
    actualEnhancedOCoefficients n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
      Real Graph Proper Adj Image Derivation Boundary Projection OCoefficientExact OCoefficientBounded :=
  (moduleCoefficientComparison n X Real IX Graph Geometry Boundary Projection
    OCoefficientExact OAllBounded OFactor).app
      ⟨actualEnhancedORaw n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
        Real Graph Proper Adj Image Derivation, BoundedO⟩

/-- The actual source O^E specializes the computed reconstruction target. -/
def actualReconstructionTarget :
    DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)) :=
  originalReconstructionTarget n X Real IX Graph Geometry Ordinary Normalize BetaExact Representatives
    (actualEnhancedO n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
      Real Graph Proper Adj Image Derivation Geometry BoundedO)
    CoefficientExact CoefficientBounded Boundary Projection M BoundedSolution

/-- The source reconstruction map uses the actual computed O^E and original native D-module evaluation. -/
def actualReconstructionMap :=
  originalReconstructionMap n X Real IX Graph Geometry Ordinary Normalize BetaExact Representatives
    (actualEnhancedO n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
      Real Graph Proper Adj Image Derivation Geometry BoundedO)
    CoefficientExact CoefficientBounded Boundary Projection M BoundedSolution

end MathlibExt.AlgebraicGeometry.NativeEnhancedHolomorphicModels
