/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NativeEnhancedHolomorphicModels
public import MathlibExt.AlgebraicGeometry.NativeDModuleDualityModels
public import MathlibExt.AlgebraicGeometry.EnhancedConstructibleIndModels
public import MathlibExt.AlgebraicGeometry.NativeOrdinaryDRSolModels
public import MathlibExt.AlgebraicGeometry.OrdinaryEnhancedEmbeddingModels
public import MathlibExt.AlgebraicGeometry.CanonicalOppositeRings

/-!
# Source compatibility outputs on the actual enhanced DR/Sol functors

The functors and every map are the already computed native operations.
Holonomicity is original local characteristic support; enhanced real
constructibility uses actual compact subanalytic cuts, Rj!, closed-half-
line filtered colimits and the original real convolution. The outputs
record source full faithfulness, constructibility and the exact
Sol(M) = DR(D_X M)[-dim X] normalization. Provider proofs are separate.

General regular holonomicity uses the sourced local good-filtration
criterion on the full native D-module carrier. The regular comparison
is a natural isomorphism with actual ordinary DR followed by the computed
e functor, using coefficient tensor with the stable unit and no shift.

The three adjoint-existence hypotheses (the left adjoint of the enhanced
quotient, the internal Hom of the coefficient tensor and the right adjoint
of the β-pullback) are the instance requests
`coefficient_enhanced_quotient_left_adjoint`, `bounded_coefficient_tensor_closed`
and `ordinary_beta_pull_right_adjoint` of NativeEnhancedRiemannHilbertWanted;
no unit of the quotient adjunctions is assumed invertible.

Source: DK1311.2374v2 Definitions4.9.1--2,9.1.1, Proposition9.1.3,
Theorems9.3.2,9.5.3; regularity source/normalization in RegularHolonomicModels.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.NativeEnhancedSourceCompatibilityWanted

open MathlibExt.AlgebraicGeometry NativeEnhancedHolomorphicModels

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

variable (Exp : ProjectiveExponentialData)
  (Plus : LeftUnitIndModuleInverseSource (pProjection X) IP DPop)
  (Minus : LeftUnitIndModuleInverseSource (pProjection X) IP DP)
  [TensorDerivationSource (InverseDX n X IX) (Mon.trivial (IndSheaf ℂ (ProductSpace X)))
    (InverseDPop X IP)]
  [TensorHomSource (InverseDX n X IX) (Mon.trivial (IndSheaf ℂ (ProductSpace X)))
    (InverseDPop X IP)]

variable [TensorDerivationSource (Mon.trivial (IndSheaf ℂ (ProductSpace X)))
    (InverseDP X IP) (InverseDXop n X IX)]
  (XBack : OppositeMonoidSource (InverseDXop n X IX) (InverseDX n X IX))
  (UnitOpp : OppositeMonoidSource (Mon.trivial (IndSheaf ℂ (ProductSpace X)))
    (Mon.trivial (IndSheaf ℂ (ProductSpace X))))
  (Back : OppositeBimoduleSource (Mon.trivial (IndSheaf ℂ (ProductSpace X)))
    (InverseDXop n X IX) (Mon.trivial (IndSheaf ℂ (ProductSpace X))) (InverseDX n X IX) UnitOpp XBack)
  [Back.functor.Additive] (BE : ExactImageSource Back.functor)

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

variable (Geometry : EnhancedModuleGeometrySource n X Real IX Graph)
  (BoundedO : IsBoundedDerived
    (Bimod (RealInverseDX n X Real IX Graph)
      (Mon.trivial (IndSheaf ℂ (enhancedSpace (TopCat.of X)).ambient)))
    (actualEnhancedORaw n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
      Real Graph Proper Adj Image Derivation))

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

variable [LeftTensorDerivationSource (RealInverseDX n X Real IX Graph) (KY X) (KY X)]
  [LeftTensorHomSource (RealInverseDX n X Real IX Graph) (KY X) (KY X)]


open NativeKernelReconstructionModels

variable [T2Space X] [(Bimod.forget (B := KY X) (KY X)).Additive]
  (CoefficientExact : ExactCoefficientSource (KY X) (KY X))
  (CoefficientBounded : BoundedCoefficientSource (KY X) (KY X) CoefficientExact)
  (Boundary : ProperSource ℂ (boundaryInclusion (enhancedSpace (TopCat.of X))))
  (Projection : InverseSource ℂ (baseProjection (TopCat.of X)))

variable
  [(coefficientEnhancedQ X CoefficientExact CoefficientBounded Boundary Projection).IsRightAdjoint]
  [∀ H : BoundedModules (KY X) (KY X),
    ((boundedCoefficientTensor n X Real IX Graph).obj H).IsLeftAdjoint]
  [(originalOrdinaryBetaPull n X Real IX Graph Geometry Ordinary Normalize BetaExact).IsLeftAdjoint]
  (M : DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
    (analyticDifferentialRing n X)))
  (BoundedSolution : IsBoundedDerived (Bimod (KY X) (KY X))
    ((actualEnhancedSolRaw n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
      Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
        Representatives).obj (Opposite.op M)))


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


variable [LocallyCompactSpace X] [SecondCountableTopology X]
  [∀ U : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{0}]
  [∀ U : Opens X,
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ (U : Opens X) (W : Over U), HasWeakSheafify
    (((Opens.grothendieckTopology X).over U).over W) AddCommGrpCat.{0}]
  [∀ (U : Opens X) (W : Over U),
    (((Opens.grothendieckTopology X).over U).over W).WEqualsLocallyBijective AddCommGrpCat.{0}]


theorem_wanted actual_holonomic_enhanced_DR_full
    (cX : CanonicalOppositeRings.CanonicalOppositeCarrier X (analyticCoefficients n X))
    (hRBack : CanonicalOppositeRings.IsInverseImageBack (realGraphInclusion (TopCat.of X) Real)
      Graph ((originalInverse (xProjection X) IX).map cX.betaMap) RBack) :
  (actualHolonomicEnhancedDR n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
    Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
      Representatives Omega OmegaFirst OmegaGraph RBack UnitOppY RightView RightExact
        CoefficientExact Boundary Projection DRBounded).Full

theorem_wanted actual_holonomic_enhanced_DR_faithful
    (cX : CanonicalOppositeRings.CanonicalOppositeCarrier X (analyticCoefficients n X))
    (hRBack : CanonicalOppositeRings.IsInverseImageBack (realGraphInclusion (TopCat.of X) Real)
      Graph ((originalInverse (xProjection X) IX).map cX.betaMap) RBack) :
  (actualHolonomicEnhancedDR n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
    Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
      Representatives Omega OmegaFirst OmegaGraph RBack UnitOppY RightView RightExact
        CoefficientExact Boundary Projection DRBounded).Faithful

open NativeDModuleDualityModels

variable [LeftTensorDerivationSource (Rop n X) (R n X) (U X)]
  [LeftTensorHomSource (Rop n X) (R n X) (U X)]
  [LeftTensorDerivationSource (R n X) (U X) (R n X)]
  [LeftTensorHomSource (R n X) (U X) (R n X)]
  (ROX : OppositeMonoidSource (R n X) (Rop n X))
  (UnitOX : OppositeMonoidSource (U X) (U X))
  (DualOpposite : OppositeBimoduleSource (U X) (R n X) (U X) (Rop n X) UnitOX ROX)
  [DualOpposite.functor.Additive] (DualOppExact : ExactImageSource DualOpposite.functor)
  [(derivedBetaModules (TopCat.of X) (analyticDifferentialRing n X)
    Ordinary Normalize BetaExact).IsLeftAdjoint]
  (DualBounded : IsBoundedDerived
    (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X) (analyticDifferentialRing n X))
    (ordinaryDualObject n X Omega ROX UnitOX DualOpposite DualOppExact
      Ordinary Normalize BetaExact M))

theorem_wanted actual_holonomic_dual_DR_shift_bounded
    (cX : CanonicalOppositeRings.CanonicalOppositeCarrier X (analyticCoefficients n X))
    (hROX : CanonicalOppositeRings.IsCanonicalOpposite cX ROX)
    (hRBack : CanonicalOppositeRings.IsInverseImageBack (realGraphInclusion (TopCat.of X) Real)
      Graph ((originalInverse (xProjection X) IX).map cX.betaMap) RBack)
    (hHolonomic : HolonomicCharacteristicSupportModels.IsBoundedHolonomic n X M) :
  IsBounded ℂ (enhancedSpace (TopCat.of X)).ambient
    ((shiftFunctor (IndDerived ℂ (enhancedSpace (TopCat.of X)).ambient) (-(n : ℤ))).obj
    ((sourceDRCoefficients n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
      Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
        Representatives Omega OmegaFirst OmegaGraph RBack UnitOppY RightView RightExact
          CoefficientExact).obj
      (ordinaryDualObject n X Omega ROX UnitOX DualOpposite DualOppExact
        Ordinary Normalize BetaExact M)))

def_wanted actual_enhanced_Sol_DR_duality_iso
    (cX : CanonicalOppositeRings.CanonicalOppositeCarrier X (analyticCoefficients n X))
    (hROX : CanonicalOppositeRings.IsCanonicalOpposite cX ROX)
    (hRBack : CanonicalOppositeRings.IsInverseImageBack (realGraphInclusion (TopCat.of X) Real)
      Graph ((originalInverse (xProjection X) IX).map cX.betaMap) RBack)
    (hHolonomic : HolonomicCharacteristicSupportModels.IsBoundedHolonomic n X M)
    (ShiftBounded : IsBounded ℂ (enhancedSpace (TopCat.of X)).ambient
      ((shiftFunctor (IndDerived ℂ (enhancedSpace (TopCat.of X)).ambient) (-(n : ℤ))).obj
    ((sourceDRCoefficients n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
      Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
        Representatives Omega OmegaFirst OmegaGraph RBack UnitOppY RightView RightExact
          CoefficientExact).obj
      (ordinaryDualObject n X Omega ROX UnitOX DualOpposite DualOppExact
        Ordinary Normalize BetaExact M)))) :
  (actualEnhancedSol n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
    Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
      Representatives CoefficientExact Boundary Projection SolBounded).obj
        (Opposite.op ⟨M, hHolonomic.1⟩) ≅
  (enhancedSourceProjection ℂ (TopCat.of X) Boundary Projection).obj
    ⟨((shiftFunctor (IndDerived ℂ (enhancedSpace (TopCat.of X)).ambient) (-(n : ℤ))).obj
    ((sourceDRCoefficients n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
      Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
        Representatives Omega OmegaFirst OmegaGraph RBack UnitOppY RightView RightExact
          CoefficientExact).obj
      (ordinaryDualObject n X Omega ROX UnitOX DualOpposite DualOppExact
        Ordinary Normalize BetaExact M))), ShiftBounded⟩

open EnhancedConstructibleIndModels EnhancedStableCoefficientModels OrdinaryIndDerivedModels
open IndSheafCoefficientModels EnhancedSheafHomModels SubanalyticIndDistributionModels
open BorderedRealSpaceModels BorderedRealTimeModels BorderedGraphKernelModels

variable [CompactSheafSource ℂ (RealInterior X)]
  [CompactSheafSource ℂ (doubleTimeSpace (TopCat.of X)).ambient]
  [CompactSheafSource ℂ (sumProduct (TopCat.of X))]

local instance wantedRCOrdinaryPreadditive : Preadditive (OrdinarySheaf ℂ (RealInterior X)) :=
  Abelian.toPreadditive

variable (IotaRC : OrdinaryIndSource ℂ (RealInterior X))
  [(ordinaryToInd ℂ (RealInterior X) IotaRC).Additive]
  (IotaExactRC : ExactImageSource (ordinaryToInd ℂ (RealInterior X) IotaRC))
  (IotaBoundedRC : BoundedIotaSource ℂ (RealInterior X) IotaRC IotaExactRC)
  (JRC : ProperSource ℂ (finiteRealInclusion X))
  [(BorderedRealConstructibleModels.ordinaryCompactifiedExtension X).Additive]
  (OrdinaryExtensionExactRC : ExactImageSource
    (BorderedRealConstructibleModels.ordinaryCompactifiedExtension X))
  (RepresentativesRC : EnhancedRepresentativeSource ℂ (TopCat.of X) Boundary Projection)
  (TensorRC : TensorSource ℂ (enhancedSpace (TopCat.of X)).ambient)
  (ClosedRC : ClosedHalfLineDiagramSource (TopCat.of X))
  (StableIotaRC : OrdinaryIndSource ℂ (enhancedSpace (TopCat.of X)).ambient)
  (ColimitRC : StableColimitSource (TopCat.of X) ClosedRC StableIotaRC)
  (CompactRC : CompactOpenCoefficientSource n X)
  (SingleRC : ConstructibleSingleSource n X ClosedRC StableIotaRC ColimitRC CompactRC)
  (GRC : TimeSumGraphSource (TopCat.of X))
  (SumTensorRC : TensorSource ℂ (sumProduct (TopCat.of X)))
  (SumInverseRC : InverseSource ℂ (firstProjection (doubleTimeSpace (TopCat.of X))
    (enhancedSpace (TopCat.of X))))
  (SumProperRC : ProperSource ℂ (secondProjection (doubleTimeSpace (TopCat.of X))
    (enhancedSpace (TopCat.of X))))
  (TimeTensorRC : TensorSource ℂ (doubleTimeSpace (TopCat.of X)).ambient)
  (FirstRC : InverseSource ℂ (timeFirst (TopCat.of X)))
  (SecondRC : InverseSource ℂ (timeSecond (TopCat.of X)))

def_wanted actual_closed_halfline_diagram : ClosedHalfLineDiagramSource (TopCat.of X)

theorem_wanted actual_compact_subanalytic_open_coefficients : CompactOpenCoefficientSource n X

theorem_wanted actual_constructible_stable_and_probe_bounds :
  ConstructibleSingleSource n X ClosedRC StableIotaRC ColimitRC CompactRC

theorem_wanted actual_ordinary_compactified_extension_additive :
  (BorderedRealConstructibleModels.ordinaryCompactifiedExtension X).Additive

theorem_wanted actual_ordinary_compactified_extension_exact : ExactImageSource
  (BorderedRealConstructibleModels.ordinaryCompactifiedExtension X)

theorem_wanted actual_ordinary_compactified_extension_bounded :
  BorderedRealConstructibleModels.BoundedOrdinaryCompactifiedExtensionSource
    X OrdinaryExtensionExactRC

variable (OrdinaryExtensionBoundedRC :
    BorderedRealConstructibleModels.BoundedOrdinaryCompactifiedExtensionSource
      X OrdinaryExtensionExactRC)
  (IotaAmbientRC : OrdinaryIndSource ℂ (enhancedSpace (TopCat.of X)).ambient)
  [(ordinaryToInd ℂ (enhancedSpace (TopCat.of X)).ambient IotaAmbientRC).Additive]
  (IotaAmbientExactRC : ExactImageSource
    (ordinaryToInd ℂ (enhancedSpace (TopCat.of X)).ambient IotaAmbientRC))
  (IotaAmbientBoundedRC : BoundedIotaSource ℂ (enhancedSpace (TopCat.of X)).ambient
    IotaAmbientRC IotaAmbientExactRC)

/-- Ordinary and Ind realizations use the same finite-real j! and all original maps. -/
def_wanted actual_ordinary_ind_compactified_extension_iso :
  BorderedRealConstructibleModels.boundedOrdinaryCompactifiedExtension
    X OrdinaryExtensionExactRC OrdinaryExtensionBoundedRC ⋙
      boundedIota ℂ (enhancedSpace (TopCat.of X)).ambient
        IotaAmbientRC IotaAmbientExactRC IotaAmbientBoundedRC ≅
    ordinaryBorderedRealization X IotaRC IotaExactRC IotaBoundedRC JRC

theorem_wanted actual_holonomic_enhanced_DR_real_constructible
    (cX : CanonicalOppositeRings.CanonicalOppositeCarrier X (analyticCoefficients n X))
    (hRBack : CanonicalOppositeRings.IsInverseImageBack (realGraphInclusion (TopCat.of X) Real)
      Graph ((originalInverse (xProjection X) IX).map cX.betaMap) RBack)
    (hHolonomic : HolonomicCharacteristicSupportModels.IsBoundedHolonomic n X M) :
  IsEnhancedRConstructible n X IotaRC IotaExactRC IotaBoundedRC JRC OrdinaryExtensionExactRC
    Boundary Projection
    RepresentativesRC TensorRC ClosedRC StableIotaRC ColimitRC CompactRC SingleRC GRC
      SumTensorRC SumInverseRC SumProperRC TimeTensorRC FirstRC SecondRC
      ((actualEnhancedDR n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
        Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
          Representatives Omega OmegaFirst OmegaGraph RBack UnitOppY RightView RightExact
            CoefficientExact Boundary Projection DRBounded).obj ⟨M, hHolonomic.1⟩)

theorem_wanted actual_holonomic_enhanced_Sol_real_constructible
    (hHolonomic : HolonomicCharacteristicSupportModels.IsBoundedHolonomic n X M) :
  IsEnhancedRConstructible n X IotaRC IotaExactRC IotaBoundedRC JRC OrdinaryExtensionExactRC
    Boundary Projection
    RepresentativesRC TensorRC ClosedRC StableIotaRC ColimitRC CompactRC SingleRC GRC
      SumTensorRC SumInverseRC SumProperRC TimeTensorRC FirstRC SecondRC
      ((actualEnhancedSol n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
        Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
          Representatives CoefficientExact Boundary Projection SolBounded).obj
            (Opposite.op ⟨M, hHolonomic.1⟩))

section RegularComparison

variable (OrdinaryStructure : StructureModuleSource X (analyticCoefficients n X))
  (OrdinaryRBack : OppositeMonoidSource
    (NativeOrdinaryDRSolModels.Rop n X) (NativeOrdinaryDRSolModels.R n X))
  (OrdinaryUnitOpp : OppositeMonoidSource
    (NativeOrdinaryDRSolModels.U X) (NativeOrdinaryDRSolModels.U X))
  (OrdinaryRightView : OppositeBimoduleSource
    (NativeOrdinaryDRSolModels.Rop n X) (NativeOrdinaryDRSolModels.U X)
    (NativeOrdinaryDRSolModels.R n X) (NativeOrdinaryDRSolModels.U X)
      OrdinaryRBack OrdinaryUnitOpp)
  [OrdinaryRightView.functor.Additive]
  (OrdinaryRightExact : ExactImageSource OrdinaryRightView.functor)
  [(Bimod.forget (B := NativeOrdinaryDRSolModels.U X) (NativeOrdinaryDRSolModels.U X)).Additive]
  (OrdinaryCoefficientExact : ExactCoefficientSource
    (NativeOrdinaryDRSolModels.U X) (NativeOrdinaryDRSolModels.U X))
  [(IndSheafAlphaBetaModels.alpha ℂ (TopCat.of X)
    (IndSpaceSource.alpha (X := TopCat.of X))).Additive]
  (OrdinaryAlphaExact : IndSheafDerivedAlphaModels.ExactAlphaSource ℂ (TopCat.of X)
    (IndSpaceSource.alpha (X := TopCat.of X)))
  [LeftTensorDerivationSource
    (NativeOrdinaryDRSolModels.U X) (NativeOrdinaryDRSolModels.R n X) (NativeOrdinaryDRSolModels.U X)]
  (OrdinaryIota : OrdinaryIndSource ℂ (TopCat.of X))
  [(ordinaryToInd ℂ (TopCat.of X) OrdinaryIota).Additive]
  (OrdinaryIotaExact : ExactImageSource (ordinaryToInd ℂ (TopCat.of X) OrdinaryIota))
  (OrdinaryIotaBounded : BoundedIotaSource ℂ (TopCat.of X) OrdinaryIota OrdinaryIotaExact)

theorem_wanted actual_regular_holonomic_ordinary_DR_bounded
    (cX : CanonicalOppositeRings.CanonicalOppositeCarrier X (analyticCoefficients n X))
    (hOrdinaryRBack : CanonicalOppositeRings.IsCanonicalBack cX OrdinaryRBack) :
  ∀ L : RegularHolonomicModels.RegularHolonomicDerived n X,
    IsBoundedDerived (OrdinarySheaf ℂ (TopCat.of X))
      ((NativeOrdinaryDRSolModels.actualOrdinaryDR n X Ordinary Normalize BetaExact
        OrdinaryStructure Omega OrdinaryRBack OrdinaryUnitOpp OrdinaryRightView OrdinaryRightExact
          OrdinaryCoefficientExact OrdinaryAlphaExact).obj L.obj)

variable (OrdinaryDRBounded : ∀ L : RegularHolonomicModels.RegularHolonomicDerived n X,
  IsBoundedDerived (OrdinarySheaf ℂ (TopCat.of X))
    ((NativeOrdinaryDRSolModels.actualOrdinaryDR n X Ordinary Normalize BetaExact
      OrdinaryStructure Omega OrdinaryRBack OrdinaryUnitOpp OrdinaryRightView OrdinaryRightExact
        OrdinaryCoefficientExact OrdinaryAlphaExact).obj L.obj))

/-- Proposition9.1.3, with actual native maps and arbitrary-support regular holonomic cohomology. -/
def_wanted actual_regular_holonomic_enhanced_DR_iso
    (cX : CanonicalOppositeRings.CanonicalOppositeCarrier X (analyticCoefficients n X))
    (hRBack : CanonicalOppositeRings.IsInverseImageBack (realGraphInclusion (TopCat.of X) Real)
      Graph ((originalInverse (xProjection X) IX).map cX.betaMap) RBack)
    (hOrdinaryRBack : CanonicalOppositeRings.IsCanonicalBack cX OrdinaryRBack) :
  actualRegularHolonomicEnhancedDR n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
    Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
      Representatives Omega OmegaFirst OmegaGraph RBack UnitOppY RightView RightExact
        CoefficientExact Boundary Projection DRBounded ≅
  NativeOrdinaryDRSolModels.actualRegularOrdinaryDR n X Ordinary Normalize BetaExact
    OrdinaryStructure Omega OrdinaryRBack OrdinaryUnitOpp OrdinaryRightView OrdinaryRightExact
      OrdinaryCoefficientExact OrdinaryAlphaExact OrdinaryDRBounded ⋙
    OrdinaryEnhancedEmbeddingModels.ordinaryEnhancedEmbedding (TopCat.of X)
      OrdinaryIota OrdinaryIotaExact OrdinaryIotaBounded Boundary Projection TensorRC
        ClosedRC StableIotaRC ColimitRC SingleRC.stableBounded

end RegularComparison

end WantedExt.AlgebraicGeometry.NativeEnhancedSourceCompatibilityWanted
