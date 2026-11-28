/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.TemperedIndBimoduleModels
public import MathlibExt.CategoryTheory.NativeEnhancedDModuleExpressions

/-!
# Actual native tempered holomorphic module construction

The source packet records the original all-chart LF quotient, its
subanalytic filtered presentation and both full local-End beta-D actions.
Conjugate O is a native ordinary Dbar module fixed on every original
coefficient section, restriction and finite operator. Its beta image and
opposite view are the actual input to the native derived module Hom.
O^t is computed from these objects; it is not a chosen degree-zero object.

Source: DK1311.2374v2 Definition5.2.1 and Section4.10;
Mathlib56a005 native module, beta, opposite, single Q and Hom, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeTemperedHolomorphicModels

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open CompactSupportIndSheaves IndSheafCoefficientModels
open NativeIndDifferentialContexts LocalBetaDifferentialActionModels
open SubanalyticIndDistributionModels TemperedDifferentialActionModels TemperedIndBimoduleModels
open ManifoldDistributionModels AnalyticChartDifferentialOperators
open MathlibExt.CategoryTheory.NativeOppositeBimoduleModels
open MathlibExt.CategoryTheory.NativeDerivedBimoduleCalculus

open scoped Manifold ContDiff

variable [∀ Z : TopCat.{0}, HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
  (n : ℕ) (M : Type) [TopologicalSpace M]
  [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) M]
  [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ M]
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
  [CompactSheafSource ℂ (TopCat.of M)]

local instance nativeTemperedIndPreadditive : Preadditive (IndSheaf ℂ (TopCat.of M)) :=
  Abelian.toPreadditive

variable [IndSpaceSource (TopCat.of M)]
  [DifferentialBetaSource M (analyticCoefficients n M)]
  [DifferentialBetaSource M (analyticConjugateCoefficients n M)]
  [OppositeDifferentialBetaSource M (analyticConjugateCoefficients n M)]

/-- Construction data chooses the actual local sources and retains every source normalization. -/
class NativeTemperedSourcePacket where
  [localCompact : ∀ U : Opens M, CompactSheafSource ℂ (TopCat.of U)]
  [localContext : ∀ U : Opens M, IndSpaceSource (TopCat.of U)]
  [localD : ∀ U : Opens M, BetaRingSource (TopCat.of U)
    (pulledRing (TopCat.of M) U (analyticDifferentialRing n M))]
  [localDbar : ∀ U : Opens M, BetaRingSource (TopCat.of U)
    (pulledRing (TopCat.of M) U (analyticConjugateOppositeRing n M))]
  chartOpen : ChartOpenSource n M
  density : TestDensityTransferSource n M chartOpen
  compactOpen : CompactOpenCoefficientSource n M
  quotientRestriction : TemperedRestrictionSource n M chartOpen density
  indDistribution : TemperedIndDistributionSource n M compactOpen chartOpen density quotientRestriction
  chartProjection : TemperedChartProjectionSource n M chartOpen density
  localHolomorphic : TemperedOperatorSource n M chartOpen density chartProjection
    (analyticCoefficients n M) (holomorphicChartValue n M) false
  localConjugate : TemperedOperatorSource n M chartOpen density chartProjection
    (analyticConjugateCoefficients n M) (conjugateChartValue n M) true
  bimodule : TemperedDoubleModuleSource n M compactOpen chartOpen density quotientRestriction
    indDistribution chartProjection localHolomorphic localConjugate

attribute [instance] NativeTemperedSourcePacket.localCompact
attribute [instance_reducible, instance] NativeTemperedSourcePacket.localContext
  NativeTemperedSourcePacket.localD NativeTemperedSourcePacket.localDbar

def actualDistributionModule (S : NativeTemperedSourcePacket n M) : TemperedBimodule n M :=
  letI := S.localCompact
  letI := S.localContext
  letI := S.localD
  letI := S.localDbar
  S.bimodule.object

/-- Actual ordinary Obar, including every original finite Dbar operator on every section. -/
structure ConjugateStructureModuleSource where
  object : DifferentialOperatorSheaves.DModule ℂ M (analyticConjugateCoefficients n M)
  sections : ∀ U : Opens M, object.val.obj (op U) ≃+
    (analyticConjugateCoefficients n M).obj (op U)
  restriction : ∀ (U V : Opens M) (h : V ≤ U) (s : object.val.obj (op U)),
    sections V ((object.val.map (homOfLE h).op).hom s) =
      (analyticConjugateCoefficients n M).map (homOfLE h).op (sections U s)
  operator : ∀ (U : Opens M)
      (P : DifferentialOperatorSheaves.finiteOperatorRing ℂ M
        (analyticConjugateCoefficients n M) U) (s : object.val.obj (op U)),
    sections U (((toSheafify (Opens.grothendieckTopology M)
      (DifferentialOperatorSheaves.operatorPresheaf ℂ M
        (analyticConjugateCoefficients n M))).app (op U)).hom P • s) =
        P.val.val ⟨U, le_refl U⟩ (sections U s)

abbrev DX := betaRing (TopCat.of M) (analyticDifferentialRing n M)
abbrev Dbar := betaRing (TopCat.of M) (analyticConjugateDifferentialRing n M)
abbrev DbarOp := betaRing (TopCat.of M) (analyticConjugateOppositeRing n M)
abbrev K := coefficientMonoid (TopCat.of M)

variable (N : OrdinaryBetaModuleSource (TopCat.of M) (analyticConjugateDifferentialRing n M))
  (RO : OppositeMonoidSource (Dbar n M) (DbarOp n M))
  (KO : OppositeMonoidSource (K M) (K M))
  (O : OppositeBimoduleSource (Dbar n M) (K M) (DbarOp n M) (K M) RO KO)

local instance nativeConjugatePreadditive (A B : Mon (IndSheaf ℂ (TopCat.of M))) :
    Preadditive (Bimod A B) := Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

def conjugateBetaInput (S : ConjugateStructureModuleSource n M) :
    DerivedCategory (Bimod (K M) (DbarOp n M)) :=
  (DerivedCategory.singleFunctor (Bimod (K M) (DbarOp n M)) 0).obj
    (O.functor.obj ((betaModules (TopCat.of M) (analyticConjugateDifferentialRing n M) N).obj S.object))

variable [TensorDerivationSource (DX n M) (K M) (DbarOp n M)]
  [TensorHomSource (DX n M) (K M) (DbarOp n M)]

/-- The exact Definition5.2.1 object in the actual native beta-D module derived category. -/
def actualTemperedO (S : NativeTemperedSourcePacket n M) (C : ConjugateStructureModuleSource n M) :
    DerivedCategory (Bimod (DX n M) (K M)) :=
  MathlibExt.CategoryTheory.NativeEnhancedDModuleExpressions.temperedHolomorphic
    (DX n M) (K M) (DbarOp n M) (conjugateBetaInput n M N RO KO O C)
      ((DerivedCategory.singleFunctor (TemperedBimodule n M) 0).obj (actualDistributionModule n M S))

end MathlibExt.AlgebraicGeometry.NativeTemperedHolomorphicModels
