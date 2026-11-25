/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NativeOrdinaryDRSolModels
public import MathlibExt.AlgebraicGeometry.NativeRationalCurveModuleModels
public import MathlibExt.AlgebraicGeometry.CanonicalOppositeRings

/-!
# Full native D-module curve realization and gauge requests

The connection carrier is the actual full-D module on original
holomorphic vector sections. The compared DR/Sol objects are the native
Omega tensor and left-D module Hom with actual beta/alpha. DR is compared
with the original two-term complex shifted [1]; Sol with the actual
-transpose(A) horizontal sheaf in degree zero. Gauge maps retain every
original matrix section value and full native D-linearity.
Source: DK1311.2374v2 Section2.5/Definition9.1.1 and the original
RegularSingularConnections rational punctured-line source scope.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.NativeRationalCurveDModuleWanted

open MathlibExt.AlgebraicGeometry
open NativeOrdinaryDRSolModels NativeRationalCurveModuleModels NativeRationalCurveRealizations
open RegularSingularConnections

def_wanted actual_curve_complex_atlas (S : Finset ℂ) : CurveComplexSource S

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves NativeIndDifferentialContexts NativeBetaModuleDerivedModels
open NativeOmegaTransferModels HolomorphicCotangentModuleModels
open MathlibExt.CategoryTheory.NativeDerivedBimoduleCalculus
open MathlibExt.CategoryTheory.NativeOppositeBimoduleModels
open MathlibExt.CategoryTheory.NativeRingedAdjointImageModels
open NativeOrdinaryDifferentialRepresentations IndSheafDerivedAlphaModels
open MathlibExt.CategoryTheory.NativeBoundedBimoduleModels
open scoped Manifold ContDiff

variable (S : Finset ℂ) [CurveComplexSource S]
  [HolomorphicCoefficientSheaves.SheafCondition
    (TemperedDistributionSectionModels.ComplexCoordinates 1) (puncturedLine S)]
  [CotangentSectionCalculus (n := 1) (M := (puncturedLine S))] [CotangentSheafCondition (n := 1) (M := (puncturedLine S))]
  [HasSheafify (Opens.grothendieckTopology (puncturedLine S)) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology (puncturedLine S)) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology (puncturedLine S)).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasSheafify (Opens.grothendieckTopology (puncturedLine S)) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ (TopCat.of (puncturedLine S))] [CX : IndSpaceSource (TopCat.of (puncturedLine S))]
  [DifferentialBetaSource (puncturedLine S) (analyticCoefficients 1 (puncturedLine S))]
  [OppositeDifferentialBetaSource (puncturedLine S) (analyticCoefficients 1 (puncturedLine S))]

local instance dualityPreadditive (A B : Mon (IndSheaf ℂ (TopCat.of (puncturedLine S)))) :
    Preadditive (Bimod A B) := Abelian.toPreadditive
local instance ordinaryDualityPreadditive :
    Preadditive (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of (puncturedLine S))
      (analyticDifferentialRing 1 (puncturedLine S))) := Abelian.toPreadditive
local instance ordinaryScalarIndPreadditive : Preadditive (IndSheaf ℂ (TopCat.of (puncturedLine S))) :=
  Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard


variable (Ordinary : OrdinaryBetaModuleSource (TopCat.of (puncturedLine S)) (analyticDifferentialRing 1 (puncturedLine S)))
  (Normalize : BetaUnitNormalizationSource (TopCat.of (puncturedLine S)) (analyticDifferentialRing 1 (puncturedLine S)))
  [(betaUnitModules (TopCat.of (puncturedLine S)) (analyticDifferentialRing 1 (puncturedLine S)) Ordinary Normalize).Additive]
  (BetaExact : ExactImageSource
    (betaUnitModules (TopCat.of (puncturedLine S)) (analyticDifferentialRing 1 (puncturedLine S)) Ordinary Normalize))
  (Structure : StructureModuleSource (puncturedLine S) (analyticCoefficients 1 (puncturedLine S)))

variable (Omega : OmegaTransferSource 1 (puncturedLine S))
  [LeftTensorDerivationSource (Rop 1 (puncturedLine S)) (R 1 (puncturedLine S)) (U (puncturedLine S))]
  (RBack : OppositeMonoidSource (Rop 1 (puncturedLine S)) (R 1 (puncturedLine S)))
  (UnitOpp : OppositeMonoidSource (U (puncturedLine S)) (U (puncturedLine S)))
  (RightView : OppositeBimoduleSource (Rop 1 (puncturedLine S)) (U (puncturedLine S)) (R 1 (puncturedLine S)) (U (puncturedLine S)) RBack UnitOpp)
  [RightView.functor.Additive] (RightExact : ExactImageSource RightView.functor)

variable [(Bimod.forget (B := U (puncturedLine S)) (U (puncturedLine S))).Additive]
  (CoefficientExact : ExactCoefficientSource (U (puncturedLine S)) (U (puncturedLine S)))
  [(IndSheafAlphaBetaModels.alpha ℂ (TopCat.of (puncturedLine S)) CX.alpha).Additive]
  (AlphaExact : ExactAlphaSource ℂ (TopCat.of (puncturedLine S)) CX.alpha)

variable [LeftTensorDerivationSource (U (puncturedLine S)) (R 1 (puncturedLine S)) (U (puncturedLine S))]

variable [LeftTensorDerivationSource (R 1 (puncturedLine S)) (U (puncturedLine S)) (U (puncturedLine S))]
  [LeftTensorHomSource (R 1 (puncturedLine S)) (U (puncturedLine S)) (U (puncturedLine S))]

def_wanted actual_curve_coordinate : CurveCoordinateSource S

def_wanted actual_curve_native_connection {r : ℕ}
    (A : Matrix (Fin r) (Fin r) RationalFunctions) (C : CurveCoordinateSource S)
    (hA : PolesWithin S A) : RationalConnectionModuleSource S A hA C

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) RationalFunctions) (hA : PolesWithin S A)
  (C : CurveCoordinateSource S) (MA : RationalConnectionModuleSource S A hA C)

/-- **De Rham complex of a rational connection on the punctured line.** Let $S ⊂ ℂ$ be a finite
set, fix the given analytic and D-module interface data on the punctured line $ℂ \setminus S$, and
let $A$ be an $r × r$ matrix of rational functions with poles in $S$, with a given connection
module $M_A$ (`RationalConnectionModuleSource`) and analytic connection de Rham data $D$
(`AnalyticConnectionDeRhamData`). Assume that the given opposite-ring data `RBack` is the
canonical anti-identification of the opposite differential ring (`IsCanonicalBack`, for a
canonical opposite carrier $c$). Then: an isomorphism, in the derived category, from the ordinary
de Rham complex `actualOrdinaryDR` of $M_A$ (placed in degree zero) to the two-term de Rham
complex of $D$ shifted by one (`ordinaryCurveDR`). -/
def_wanted actual_curve_native_DR_iso (D : AnalyticConnectionDeRhamData S r A hA)
    (c : CanonicalOppositeRings.CanonicalOppositeCarrier (puncturedLine S)
      (analyticCoefficients 1 (puncturedLine S)))
    (hRBack : CanonicalOppositeRings.IsCanonicalBack c RBack) :
  (actualOrdinaryDR 1 (puncturedLine S) Ordinary Normalize BetaExact Structure Omega
    RBack UnitOpp RightView RightExact CoefficientExact AlphaExact).obj
      ((DerivedCategory.singleFunctor (RingedComplexCoefficientModels.OrdinaryModule
        (TopCat.of (puncturedLine S)) (analyticDifferentialRing 1 (puncturedLine S))) 0).obj
          MA.object) ≅ ordinaryCurveDR S A hA D

def_wanted actual_curve_native_Sol_iso :
  (actualOrdinarySol 1 (puncturedLine S) Ordinary Normalize BetaExact Structure
    CoefficientExact AlphaExact).obj
      (Opposite.op ((DerivedCategory.singleFunctor (RingedComplexCoefficientModels.OrdinaryModule
        (TopCat.of (puncturedLine S)) (analyticDifferentialRing 1 (puncturedLine S))) 0).obj
          MA.object)) ≅ ordinaryCurveSol S A hA

def_wanted actual_curve_native_gauge (δ : RationalDerivative) {s : ℕ}
    (B : Matrix (Fin s) (Fin s) RationalFunctions)
    (G : Matrix (Fin s) (Fin r) RationalFunctions)
    (hB : PolesWithin S B) (hG : PolesWithin S G)
    (MB : RationalConnectionModuleSource S B hB C)
    (hHorizontal : HorizontalMatrix δ A B G) : NativeCurveGaugeSource S A hA C B hB G hG MA MB

end WantedExt.AlgebraicGeometry.NativeRationalCurveDModuleWanted
