/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ProjectiveExponentialSectionModels
public import MathlibExt.AlgebraicGeometry.NativeBetaModuleDerivedModels
public import MathlibExt.AlgebraicGeometry.NativeIndModuleInverseModels
public import MathlibExt.CategoryTheory.NativeOppositeBimoduleModels
public import MathlibExt.AlgebraicGeometry.CanonicalOppositeRings

/-!
# Full native exp(tau) and r(exp(-tau)) product inputs

The source packet retains the actual meromorphic coefficient sheaves,
all finite P operators, the actual Omega_P tensor, d-tau frame and formal
transpose. Beta, elementary opposite views and the original Ind inverse
image compute the two projected native objects. No final P-action is lost.
Source: DK1311.2374v2 Definition8.2.1; Mathlib56a005, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeProjectiveExponentialPackets

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves ProjectiveExponentialSectionModels NativeIndDifferentialContexts
open NativeBetaModuleDerivedModels NativeIndModuleInverseModels
open HolomorphicCotangentModuleModels
open MathlibExt.CategoryTheory.NativeOppositeBimoduleModels
open scoped Manifold ContDiff

variable [ProjectiveComplexSource]
  [HolomorphicCoefficientSheaves.SheafCondition ProjectiveCoordinates ProjectiveLine]
  [CotangentSectionCalculus (n := 1) (M := ProjectiveLine)]
  [CotangentSheafCondition (n := 1) (M := ProjectiveLine)]
  [HasSheafify (Opens.grothendieckTopology ProjectiveLine) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology ProjectiveLine) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology ProjectiveLine).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasSheafify (Opens.grothendieckTopology ProjectiveLine) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ (TopCat.of ProjectiveLine)] [IndSpaceSource (TopCat.of ProjectiveLine)]
  [DifferentialBetaSource ProjectiveLine (analyticCoefficients 1 ProjectiveLine)]
  [OppositeDifferentialBetaSource ProjectiveLine (analyticCoefficients 1 ProjectiveLine)]

abbrev DP := betaRing (TopCat.of ProjectiveLine) (analyticDifferentialRing 1 ProjectiveLine)
abbrev DPop := betaRing (TopCat.of ProjectiveLine) (analyticOppositeDifferentialRing 1 ProjectiveLine)
abbrev KP := Mon.trivial (IndSheaf ℂ (TopCat.of ProjectiveLine))

class ProjectiveExponentialData where
  plus : ExponentialDModuleSource 1
  minus : ExponentialDModuleSource (-1)
  tauDerivative : TauDerivativeSource
  topform : TauTopFormSource
  formalTranspose : ∀ (U : Opens ProjectiveLine) (hfinite : OnePoint.infty ∉ U),
    LocalFormalTransposeSource U hfinite tauDerivative
  rightMinus : RightNegativeExponentialSource minus tauDerivative topform formalTranspose
  ordinaryLeft : OrdinaryBetaModuleSource (TopCat.of ProjectiveLine)
    (analyticDifferentialRing 1 ProjectiveLine)
  ordinaryRight : OrdinaryBetaModuleSource (TopCat.of ProjectiveLine)
    (analyticOppositeDifferentialRing 1 ProjectiveLine)
  normalizeLeft : BetaUnitNormalizationSource (TopCat.of ProjectiveLine)
    (analyticDifferentialRing 1 ProjectiveLine)
  normalizeRight : BetaUnitNormalizationSource (TopCat.of ProjectiveLine)
    (analyticOppositeDifferentialRing 1 ProjectiveLine)
  opposite : OppositeMonoidSource DP DPop
  oppositeBack : OppositeMonoidSource DPop DP
  /-- Both opposite structures are the canonical anti-identification and its inverse. -/
  canonical : CanonicalOppositeRings.CanonicalOppositeCarrier ProjectiveLine
    (analyticCoefficients 1 ProjectiveLine)
  opposite_canonical : CanonicalOppositeRings.IsCanonicalOpposite canonical opposite
  oppositeBack_canonical : CanonicalOppositeRings.IsCanonicalBack canonical oppositeBack
  unitOpposite : OppositeMonoidSource KP KP
  plusView : OppositeBimoduleSource DP KP DPop KP opposite unitOpposite
  minusView : OppositeBimoduleSource DPop KP DP KP oppositeBack unitOpposite

variable (S : ProjectiveExponentialData)

def plusBetaRight : Bimod KP DPop :=
  S.plusView.functor.obj
    ((betaUnitModules (TopCat.of ProjectiveLine) (analyticDifferentialRing 1 ProjectiveLine)
      S.ordinaryLeft S.normalizeLeft).obj S.plus.object)

def minusBetaRight : Bimod KP DP :=
  S.minusView.functor.obj
    ((betaUnitModules (TopCat.of ProjectiveLine) (analyticOppositeDifferentialRing 1 ProjectiveLine)
      S.ordinaryRight S.normalizeRight).obj S.rightMinus.object)

variable (Y : TopCat.{0})
  [HasSheafify (Opens.grothendieckTopology Y) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ Y] [IndSpaceSource Y] (f : Y ⟶ TopCat.of ProjectiveLine)
  (I : InverseMonoidalSource f)
  (Plus : LeftUnitIndModuleInverseSource f I DPop)
  (Minus : LeftUnitIndModuleInverseSource f I DP)

local instance projectedExpPreadditive (R T : Mon (IndSheaf ℂ Y)) : Preadditive (Bimod R T) :=
  Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

def projectedPlus : DerivedCategory (Bimod (Mon.trivial (IndSheaf ℂ Y)) (inverseRing f I DPop)) :=
  (DerivedCategory.singleFunctor (Bimod (Mon.trivial (IndSheaf ℂ Y)) (inverseRing f I DPop)) 0).obj
    ((leftUnitIndModuleInverse f I DPop Plus).obj (plusBetaRight S))

def projectedRightMinus : DerivedCategory (Bimod (Mon.trivial (IndSheaf ℂ Y)) (inverseRing f I DP)) :=
  (DerivedCategory.singleFunctor (Bimod (Mon.trivial (IndSheaf ℂ Y)) (inverseRing f I DP)) 0).obj
    ((leftUnitIndModuleInverse f I DP Minus).obj (minusBetaRight S))

end MathlibExt.AlgebraicGeometry.NativeProjectiveExponentialPackets
