/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeTemperedHolomorphicModels
public import MathlibExt.AlgebraicGeometry.NativeBetaModuleDerivedModels
public import MathlibExt.CategoryTheory.NativeRingedAdjointImageModels
public import MathlibExt.AlgebraicGeometry.CanonicalOppositeRings

/-!
# Complete native source data for the actual tempered O object

The packet retains all source-qualified distribution and Obar data. Its
object is the prescribed actual Dbar-Hom expression, then its coefficient
ring is normalized by the canonical native mapMon unit.
Source: DK1311.2374v2 Definition5.2.1; Mathlib56a005, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeTemperedOPackets

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves NativeIndDifferentialContexts NativeTemperedHolomorphicModels
open NativeBetaModuleDerivedModels
open MathlibExt.CategoryTheory.NativeOppositeBimoduleModels
open MathlibExt.CategoryTheory.NativeDerivedBimoduleCalculus
open MathlibExt.CategoryTheory.NativeRingedAdjointImageModels

open scoped Manifold ContDiff

variable [∀ Z : TopCat.{0}, HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
  (n : ℕ) (M : Type) [TopologicalSpace M]
  [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) M]
  [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ M]
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
  [CompactSheafSource ℂ (TopCat.of M)] [IndSpaceSource (TopCat.of M)]
  [DifferentialBetaSource M (analyticCoefficients n M)]
  [DifferentialBetaSource M (analyticConjugateCoefficients n M)]
  [OppositeDifferentialBetaSource M (analyticConjugateCoefficients n M)]

local instance packetPreadditive (R S : Mon (IndSheaf ℂ (TopCat.of M))) : Preadditive (Bimod R S) :=
  Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

class TemperedOData where
  distribution : NativeTemperedSourcePacket n M
  conjugate : ConjugateStructureModuleSource n M
  ordinary : OrdinaryBetaModuleSource (TopCat.of M) (analyticConjugateDifferentialRing n M)
  conjugateOpposite : OppositeMonoidSource (Dbar n M) (DbarOp n M)
  /-- The conjugate opposite structure is the canonical anti-identification. -/
  conjugateCanonical : CanonicalOppositeRings.CanonicalOppositeCarrier M
    (analyticConjugateCoefficients n M)
  conjugateOpposite_canonical :
    CanonicalOppositeRings.IsCanonicalOpposite conjugateCanonical conjugateOpposite
  coefficientOpposite : OppositeMonoidSource (K M) (K M)
  conjugateView : OppositeBimoduleSource (Dbar n M) (K M) (DbarOp n M) (K M)
    conjugateOpposite coefficientOpposite
  [tensor : TensorDerivationSource (DX n M) (K M) (DbarOp n M)]
  [hom : TensorHomSource (DX n M) (K M) (DbarOp n M)]
  unitNormalization : BetaUnitNormalizationSource (TopCat.of M) (analyticDifferentialRing n M)
  [unitAdditive : unitNormalization.restriction.functor.Additive]
  unitExact : ExactImageSource unitNormalization.restriction.functor

variable (S : TemperedOData n M)

def temperedOWithBetaUnit : DerivedCategory (Bimod (DX n M) (K M)) :=
  letI := S.tensor
  letI := S.hom
  actualTemperedO n M S.ordinary S.conjugateOpposite S.coefficientOpposite S.conjugateView
    S.distribution S.conjugate

def temperedOWithUnit :
    DerivedCategory (Bimod (DX n M) (Mon.trivial (IndSheaf ℂ (TopCat.of M)))) :=
  letI := S.unitAdditive
  (derivedExactImage S.unitNormalization.restriction.functor S.unitExact).obj
    (temperedOWithBetaUnit n M S)

end MathlibExt.AlgebraicGeometry.NativeTemperedOPackets
