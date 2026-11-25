/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NativeEnhancedHolomorphicModels
public import MathlibExt.AlgebraicGeometry.HolonomicCharacteristicSupportModels
public import MathlibExt.AlgebraicGeometry.CanonicalOppositeRings

/-!
# Source-qualified enhanced Riemann--Hilbert reconstruction request

The requested output is IsIso of the original D-module evaluation map
already constructed from the actual O^E graph Hom[2] representative,
native module-Hom counit, the native ambient tensor-Hom mate and the
actual beta-pi projection adjunction. Holonomicity is the actual local
good-filtration/characteristic-support property. The comparison map is
not supplied as an independent oracle or assumed invertible. The request is
that this ringed mate is an isomorphism; its compatibility with the canonical
scalar morphism of Proposition9.5.1 is a separate question, not part of it.

The adjoints the reconstruction map is built from (the left adjoint of the
enhanced quotient, the internal Hom of the coefficient tensor and the right
adjoint of the β-pullback) are requested below and passed to the final
request as those named holes; no unit of the quotient adjunctions is assumed
invertible.

The structural classes assumed below are not free hypotheses: each is supplied
by a direct request, and the statements are conditional only on those requests.
`CompactSheafSource` is `IndSheafSourceRequests.actual_compact_sheaf_source`;
`IndSpaceSource`, `DifferentialBetaSource` and `OppositeDifferentialBetaSource`
are `actual_ind_space_context`, `actual_differential_beta_ring` and
`actual_opposite_differential_beta_ring` (NativeAnalyticIndConstructionWanted);
the cotangent calculus is in HarmonicHolomorphicModulesWanted; and
`ProjectiveComplexSource`, `ProductComplexSource`, `OrdinaryInverseMonoidalSource`
and `PulledBetaRingSource` are requested in ProjectiveProductSourceRequests. The
complex-structure classes pin the standard structures (their coordinate maps
and projections are holomorphic), so the statements do not depend on the chosen
instance. The meromorphic coefficient algebra closure is proved.

Source: DK1311.2374v2 Proposition9.5.1, Theorem9.5.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.NativeEnhancedRiemannHilbertWanted

open MathlibExt.AlgebraicGeometry
open NativeEnhancedHolomorphicModels

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

/-- The enhanced quotient functor, from the bounded derived category of ind-sheaves of
$\mathbb{C}$-vector spaces on $X \times \overline{\mathbb{R}}$ (as bimodules over the unit) to
enhanced ind-sheaves on $X$, has a left adjoint, the functor `L^E` of D'Agnolo--Kashiwara
(arXiv:1311.2374v2, §4). As in D'Agnolo--Kashiwara, $X$ is a good space: a Hausdorff,
second-countable complex manifold of dimension $n$. -/
theorem_wanted coefficient_enhanced_quotient_left_adjoint [T2Space X] [SecondCountableTopology X]
    [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ X] :
  (coefficientEnhancedQ X CoefficientExact CoefficientBounded Boundary Projection).IsRightAdjoint

/-- Tensoring with a bounded coefficient complex has a right adjoint, the internal Hom of
ind-sheaf modules (Kashiwara--Schapira, Ind-sheaves; D'Agnolo--Kashiwara, §4). -/
theorem_wanted bounded_coefficient_tensor_closed :
  ∀ H : BoundedModules (KY X) (KY X),
    ((boundedCoefficientTensor n X Real IX Graph).obj H).IsLeftAdjoint

/-- The β-pullback of D-modules has a right adjoint: `β` is left adjoint to `α`, and the inverse
images are left adjoint to the direct images (Kashiwara--Schapira, Ind-sheaves). -/
theorem_wanted ordinary_beta_pull_right_adjoint :
  (originalOrdinaryBetaPull n X Real IX Graph Geometry Ordinary Normalize BetaExact).IsLeftAdjoint

variable
  (M : DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
    (analyticDifferentialRing n X)))
  (BoundedSolution : IsBoundedDerived (Bimod (KY X) (KY X))
    ((actualEnhancedSolRaw n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
      Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
        Representatives).obj (Opposite.op M)))

/-- Complete carrier constructors retain all original source normalizations. -/
def_wanted actual_tempered_O_packet [LocallyCompactSpace X]
    [SecondCountableTopology X]
    [DifferentialBetaSource X (analyticConjugateCoefficients n X)]
    [OppositeDifferentialBetaSource X (analyticConjugateCoefficients n X)] : TemperedOData n X

def_wanted actual_projective_exponential_packet : ProjectiveExponentialData

def_wanted actual_product_operator_views :
  ProductModuleViewSource n X IX IP NX NP PX PP Structure Operators MX MP

def_wanted actual_native_topform_transfer : OmegaTransferSource n X

def_wanted actual_enhanced_module_geometry : EnhancedModuleGeometrySource n X Real IX Graph

theorem_wanted actual_enhanced_module_representatives :
  ModuleRepresentativeSource (RealInverseDX n X Real IX Graph) (KY X)
    (nativeBoundaryImage n X Real IX Graph Geometry) (nativeBaseInverse n X Real IX Graph Geometry)

theorem_wanted actual_enhanced_O_bounded : IsBoundedDerived
    (Bimod (RealInverseDX n X Real IX Graph) (KY X))
    (actualEnhancedORaw n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
      Real Graph Proper Adj Image Derivation)

theorem_wanted actual_enhanced_O_right_bounded
    (cX : CanonicalOppositeRings.CanonicalOppositeCarrier X (analyticCoefficients n X))
    (hXBack : CanonicalOppositeRings.IsInverseImageBack (xProjection X) IX cX.betaMap XBack) :
    IsBoundedDerived
    (Bimod (RealInverseDX n X Real IX Graph) (KY X))
    (actualEnhancedORightRaw n X IX IP NX NP PX PP Structure Operators MX MP V Ot TE
      Exp Minus XBack UnitOpp Back BE Real Graph Proper Adj Image Derivation)

def_wanted actual_enhanced_O_right_iso
    (cX : CanonicalOppositeRings.CanonicalOppositeCarrier X (analyticCoefficients n X))
    (hXBack : CanonicalOppositeRings.IsInverseImageBack (xProjection X) IX cX.betaMap XBack)
    (RightBounded : IsBoundedDerived
    (Bimod (RealInverseDX n X Real IX Graph) (KY X))
    (actualEnhancedORightRaw n X IX IP NX NP PX PP Structure Operators MX MP V Ot TE
      Exp Minus XBack UnitOpp Back BE Real Graph Proper Adj Image Derivation)) :
  actualEnhancedO n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
    Real Graph Proper Adj Image Derivation Geometry BoundedO ≅
  actualEnhancedORight n X IX IP NX NP PX PP Structure Operators MX MP V Ot TE Exp Minus
    XBack UnitOpp Back BE Real Graph Proper Adj Image Derivation Geometry RightBounded

section BorderedRightRealization

variable [(Bimod.forget (B := KY X) (RealInverseDX n X Real IX Graph)).Additive]
  (BorderedCoefficientExact : ExactCoefficientSource (RealInverseDX n X Real IX Graph) (KY X))
  (BorderedCoefficientBounded : BoundedCoefficientSource
    (RealInverseDX n X Real IX Graph) (KY X) BorderedCoefficientExact)

/-- Definition8.2.1/Theorem8.2.2 compare these objects in the bordered coefficient category. -/
def_wanted actual_right_local_O_bordered_realization
    (cX : CanonicalOppositeRings.CanonicalOppositeCarrier X (analyticCoefficients n X))
    (hXBack : CanonicalOppositeRings.IsInverseImageBack (xProjection X) IX cX.betaMap XBack)
    (RightBounded : IsBoundedDerived (Bimod (RealInverseDX n X Real IX Graph) (KY X))
      (actualEnhancedORightRaw n X IX IP NX NP PX PP Structure Operators MX MP V Ot TE
        Exp Minus XBack UnitOpp Back BE Real Graph Proper Adj Image Derivation)) :
  (coefficientBorderedProjection n X Real IX Graph Boundary
    BorderedCoefficientExact BorderedCoefficientBounded).obj
      ((moduleRightRepresentative (RealInverseDX n X Real IX Graph) (KY X)
        (nativeBoundaryImage n X Real IX Graph Geometry) (nativeBaseInverse n X Real IX Graph Geometry)
          Representatives).obj
            (actualEnhancedO n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
              Real Graph Proper Adj Image Derivation Geometry BoundedO)) ≅
  (coefficientBorderedProjection n X Real IX Graph Boundary
    BorderedCoefficientExact BorderedCoefficientBounded).obj
      ⟨actualEnhancedORightRaw n X IX IP NX NP PX PP Structure Operators MX MP V Ot TE
        Exp Minus XBack UnitOpp Back BE Real Graph Proper Adj Image Derivation, RightBounded⟩

end BorderedRightRealization

variable [LocallyCompactSpace X] [SecondCountableTopology X]
  [∀ U : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{0}]
  [∀ U : Opens X,
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ (U : Opens X) (W : Over U), HasWeakSheafify
    (((Opens.grothendieckTopology X).over U).over W) AddCommGrpCat.{0}]
  [∀ (U : Opens X) (W : Over U),
    (((Opens.grothendieckTopology X).over U).over W).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- For a bounded holonomic object $M$ of the derived category of $\mathcal{D}_X$-modules whose
enhanced solution complex is bounded (`BoundedSolution`): the $\beta$-pullback of
$\mathcal{D}$-modules has a right adjoint (the statement of `ordinary_beta_pull_right_adjoint`),
and, for this right adjoint, the reconstruction map of $M$ built from the enhanced ind-sheaf
$\mathcal{O}^E_X$ of tempered holomorphic functions is an isomorphism (the ringed form of
D'Agnolo--Kashiwara, Theorem 9.5.3). The reconstruction map is formed with the left adjoint of the
enhanced quotient functor (`coefficient_enhanced_quotient_left_adjoint`), the internal Hom right
adjoint to tensoring with a bounded coefficient complex (`bounded_coefficient_tensor_closed`) and
the right adjoint of the $\beta$-pullback. -/
theorem_wanted actual_holonomic_reconstruction_isIso
    (hHolonomic : HolonomicCharacteristicSupportModels.IsBoundedHolonomic n X M) :
  (originalOrdinaryBetaPull n X Real IX Graph Geometry Ordinary Normalize BetaExact).IsLeftAdjoint ∧
    ∀ hBetaPull : (originalOrdinaryBetaPull n X Real IX Graph Geometry Ordinary Normalize
      BetaExact).IsLeftAdjoint,
    IsIso (actualReconstructionMap n X IX IP NX NP PX PP Structure Operators MX MP V Ot HE Exp Plus
      Real Graph Proper Adj Image Derivation Geometry BoundedO Ordinary Normalize BetaExact
        Representatives CoefficientExact CoefficientBounded Boundary Projection M BoundedSolution
        (quotientLeftAdjoint := ❰coefficient_enhanced_quotient_left_adjoint❱ n X CoefficientExact
          CoefficientBounded Boundary Projection)
        (tensorClosed := ❰bounded_coefficient_tensor_closed❱ n X IX Real Graph)
        (betaPullRightAdjoint := hBetaPull))


end WantedExt.AlgebraicGeometry.NativeEnhancedRiemannHilbertWanted
