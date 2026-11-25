/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ProductDifferentialOperatorModels
public import MathlibExt.AlgebraicGeometry.NativeBetaInverseCompatibility
public import MathlibExt.AlgebraicGeometry.NativeBetaModuleDerivedModels
public import MathlibExt.AlgebraicGeometry.CanonicalOppositeRings

/-!
# Actual inverse-ring X/P views for the native product tempered object

Projected rings are the original Ind inverse mapMon images. Their maps
into full product D are computed from the whole beta/inverse natural
comparison and the fully slice-normalized ordinary ring maps. Both
operator views retain the exact original product coefficient carrier.
Their derived actions are exact cochain localization.

Source: DK1311.2374v2 Sections4.10,8.2; Mathlib56a005, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeProductModuleViews

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves NativeIndDifferentialContexts ProjectiveExponentialSectionModels
open ProductDifferentialOperatorModels NativeIndModuleInverseModels PulledBetaRingModels
open NativeBetaInverseCompatibility NativeOrdinaryDifferentialRepresentations NativeBetaModuleDerivedModels
open MathlibExt.CategoryTheory.NativeTwoOperatorModuleViews
open MathlibExt.CategoryTheory.NativeOppositeBimoduleModels
open MathlibExt.CategoryTheory.NativeRingedAdjointImageModels
open scoped Manifold ContDiff

variable [∀ Z : TopCat.{0}, HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
  (n : ℕ) (X : Type) [TopologicalSpace X]
  [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) X]
  [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ X]
  [ProjectiveComplexSource] [ProductComplexSource n X]
  [HasSheafify (Opens.grothendieckTopology X) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology ProjectiveLine) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology (X × ProjectiveLine)) RingCat.{0}]
  [CompactSheafSource ℂ (TopCat.of X)] [IndSpaceSource (TopCat.of X)]
  [CompactSheafSource ℂ (TopCat.of ProjectiveLine)] [IndSpaceSource (TopCat.of ProjectiveLine)]
  [CompactSheafSource ℂ (ProductSpace X)] [IndSpaceSource (ProductSpace X)]
  [DifferentialBetaSource X (analyticCoefficients n X)]
  [OppositeDifferentialBetaSource X (analyticCoefficients n X)]
  [DifferentialBetaSource ProjectiveLine (analyticCoefficients 1 ProjectiveLine)]
  [OppositeDifferentialBetaSource ProjectiveLine (analyticCoefficients 1 ProjectiveLine)]
  [DifferentialBetaSource (X × ProjectiveLine) (analyticCoefficients (n + 1) (X × ProjectiveLine))]
  (IX : InverseMonoidalSource (xProjection X)) (IP : InverseMonoidalSource (pProjection X))
  [OrdinaryInverseMonoidalSource (xProjection X)] [OrdinaryInverseMonoidalSource (pProjection X)]
  [PulledBetaRingSource (xProjection X) (XRing n X)]
  [PulledBetaRingSource (pProjection X) PRing]
  (NX : BetaInverseNaturalSource (xProjection X) IX)
  (NP : BetaInverseNaturalSource (pProjection X) IP)
  (PX : OrdinaryRingPullbackSource (xProjection X) (XRing n X))
  (PP : OrdinaryRingPullbackSource (pProjection X) PRing)
  (Structure : StructureModuleSource (X × ProjectiveLine)
    (analyticCoefficients (n + 1) (X × ProjectiveLine)))
  (Operators : ProductOperatorSource n X Structure)
  (MX : OrdinaryRingMapSource (ProductSpace X) (ProjectedXRing n X)
    (FullProductRing n X) Operators.xMap)
  (MP : OrdinaryRingMapSource (ProductSpace X) (ProjectedPRing X)
    (FullProductRing n X) Operators.pMap)

abbrev ProductDX := betaRing (ProductSpace X) (FullProductRing n X)
abbrev InverseDX := inverseRing (xProjection X) IX (betaRing (TopCat.of X) (XRing n X))
abbrev InverseDXop := inverseRing (xProjection X) IX
  (betaRing (TopCat.of X) (analyticOppositeDifferentialRing n X))
abbrev InverseDP := inverseRing (pProjection X) IP (betaRing (TopCat.of ProjectiveLine) PRing)
abbrev InverseDPop := inverseRing (pProjection X) IP
  (betaRing (TopCat.of ProjectiveLine) (analyticOppositeDifferentialRing 1 ProjectiveLine))

def xEmbedding : InverseDX n X IX ⟶ ProductDX n X :=
  (inverseBetaRingComparison (xProjection X) IX (XRing n X) NX PX).hom ≫
    betaRingMap (ProductSpace X) (ProjectedXRing n X) (FullProductRing n X) Operators.xMap MX

def pEmbedding : InverseDP X IP ⟶ ProductDX n X :=
  (inverseBetaRingComparison (pProjection X) IP PRing NP PP).hom ≫
    betaRingMap (ProductSpace X) (ProjectedPRing X) (FullProductRing n X) Operators.pMap MP

/-- The two operator views on the product. The opposite structures are the inverse images of the
canonical anti-identifications of the opposite differential rings of the two factors. -/
structure ProductModuleViewSource where
  pOpposite : OppositeMonoidSource (InverseDP X IP) (InverseDPop X IP)
  xOpposite : OppositeMonoidSource (InverseDX n X IX) (InverseDXop n X IX)
  pCanonical : CanonicalOppositeRings.CanonicalOppositeCarrier ProjectiveLine
    (analyticCoefficients 1 ProjectiveLine)
  xCanonical : CanonicalOppositeRings.CanonicalOppositeCarrier X (analyticCoefficients n X)
  pOpposite_canonical : CanonicalOppositeRings.IsInverseImageOpposite (pProjection X) IP
    pCanonical.betaMap pOpposite
  xOpposite_canonical : CanonicalOppositeRings.IsInverseImageOpposite (xProjection X) IX
    xCanonical.betaMap xOpposite
  commuting : CommutingEmbeddings (ProductDX n X)
    (InverseDX n X IX) (InverseDP X IP)
    (xEmbedding n X IX NX PX Structure Operators MX)
    (pEmbedding n X IP NP PP Structure Operators MP)
  homView : TwoOperatorViewSource (ProductDX n X) (Mon.trivial (IndSheaf ℂ (ProductSpace X)))
    (InverseDX n X IX) (InverseDP X IP) (InverseDPop X IP)
    (xEmbedding n X IX NX PX Structure Operators MX)
    (pEmbedding n X IP NP PP Structure Operators MP) pOpposite
  tensorView : TwoOperatorViewSource (ProductDX n X) (Mon.trivial (IndSheaf ℂ (ProductSpace X)))
    (InverseDP X IP) (InverseDX n X IX) (InverseDXop n X IX)
    (pEmbedding n X IP NP PP Structure Operators MP)
    (xEmbedding n X IX NX PX Structure Operators MX) xOpposite

end MathlibExt.AlgebraicGeometry.NativeProductModuleViews
