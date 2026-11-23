/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeHolomorphicCoefficientModules
public import MathlibExt.AlgebraicGeometry.AnalyticChartDifferentialOperators
public import MathlibExt.CategoryTheory.NativeMonoidalBimoduleMapping
public import MathlibExt.AlgebraicGeometry.GeometricDModuleFiltrations

/-!
# Actual top-form transfer with both full differential-ring actions

The carrier is beta of the original Omega tensor regular-D module.
The right action is full original D multiplication. The left opposite
action retains the negative Lie derivative and original left D action.
Coordinate Lie differentiation is computed from the actual volume-frame
determinant and original coordinate operator. Both scalar and coordinate
actions are fixed on every original pure tensor section; full local
operator generation retains all D words.

Source: DK1311.2374v2 Section2.5 and Definitions8.2.1,9.1.1;
Mathlib56a005 native covectors, O-tensor, Mon/Bimod and beta, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeOmegaTransferModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite TopologicalSpace
open CompactSupportIndSheaves NativeIndDifferentialContexts IndDifferentialModuleModels
open IndSheafMonoidalModels NativeHolomorphicCoefficientModules HolomorphicCotangentModuleModels
open AnalyticChartDifferentialOperators DifferentialOperatorSheaves DifferentialOperatorScalars
open MathlibExt.CategoryTheory.NativeMonoidalBimoduleMapping
open scoped Manifold ContDiff

variable (n : ℕ) (M : Type) [TopologicalSpace M]
  [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) M]
  [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ M]
  [HolomorphicCoefficientSheaves.SheafCondition
    (TemperedDistributionSectionModels.ComplexCoordinates n) M]
  [CotangentSectionCalculus (n := n) (M := M)] [CotangentSheafCondition (n := n) (M := M)]
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasSheafify (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ (TopCat.of M)] [CX : IndSpaceSource (TopCat.of M)]
  [DifferentialBetaSource M (analyticCoefficients n M)]
  [OppositeDifferentialBetaSource M (analyticCoefficients n M)]

abbrev OrdinaryDX := ordinaryRing (TopCat.of M) (analyticDifferentialRing n M)
  (BetaRingSource.coefficient (X := TopCat.of M) (R := analyticDifferentialRing n M))
  (BetaRingSource.monoid (X := TopCat.of M) (R := analyticDifferentialRing n M))
abbrev OrdinaryDXop := ordinaryRing (TopCat.of M) (analyticOppositeDifferentialRing n M)
  (BetaRingSource.coefficient (X := TopCat.of M) (R := analyticOppositeDifferentialRing n M))
  (BetaRingSource.monoid (X := TopCat.of M) (R := analyticOppositeDifferentialRing n M))

variable (x : M) (U : Opens M)
  (hU : (U : Set M) ⊆ (chartAt (TemperedDistributionSectionModels.ComplexCoordinates n) x).source)

/-- The volume frame is fixed by the actual chart differential determinant on every tangent tuple. -/
structure VolumeFrameSource where
  volume : (holomorphicOmega (n := n) (M := M) n).val.obj (op U)
  volumeValue : ∀ (y : U)
      (v : Fin n → TangentSpace 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) y.val),
    volume.val y v = Matrix.det (fun i j : Fin n =>
      (NormedSpace.fromTangentSpace (𝕜 := ℂ)
        ((extChartAt 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) x) y.val))
        ((mfderiv 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n)
          𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n)
          (extChartAt 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) x) y.val) (v j)) i)
  coefficients : (holomorphicOmega (n := n) (M := M) n).val.obj (op U) ≃ₗ[
    (analyticCoefficients n M).obj (op U)] (analyticCoefficients n M).obj (op U)
  coefficientValue : ∀ (form : (holomorphicOmega (n := n) (M := M) n).val.obj (op U))
      (y : U)
      (v : Fin n → TangentSpace 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) y.val),
    form.val y v = (coefficients form).val y * volume.val y v

def coordinateLie (F : VolumeFrameSource n M x U)
    (C : ChartOperatorSource n M (analyticCoefficients n M) (holomorphicChartValue n M)
      false x U hU) (i : Fin n)
    (form : (holomorphicOmega (n := n) (M := M) n).val.obj (op U)) :
    (holomorphicOmega (n := n) (M := M) n).val.obj (op U) :=
  F.coefficients.symm ((C.coordinateOperator i).val.val ⟨U, le_refl U⟩ (F.coefficients form))

def transferSection (F : Bimod (OrdinaryDXop n M) (OrdinaryDX n M))
    (underlying : F.X ≅ (rawComplexCoefficients n M).obj (omegaRegularTensor n M))
    (U : Opens M) (form : (holomorphicOmega (n := n) (M := M) n).val.obj (op U))
    (P : finiteOperatorRing ℂ M (analyticCoefficients n M) U) : F.X.presheaf.obj (op U) :=
  (underlying.inv.hom.app (op U)).hom (omegaRegularSection n M U form P)

structure OmegaTransferSource where
  ordinary : Bimod (OrdinaryDXop n M) (OrdinaryDX n M)
  underlying : ordinary.X ≅ (rawComplexCoefficients n M).obj (omegaRegularTensor n M)
  rightValue : ∀ (U : Opens M) (form : (holomorphicOmega (n := n) (M := M) n).val.obj (op U))
      (P Q : finiteOperatorRing ℂ M (analyticCoefficients n M) U),
    ordinary.actRight.hom.app (op U)
      (sourceTensorSection ℂ (TopCat.of M) ordinary.X (OrdinaryDX n M).X U
        (transferSection n M ordinary underlying U form P)
        (GeometricDModuleFiltrations.operatorValue
          (TemperedDistributionSectionModels.ComplexCoordinates n) M Q)) =
      transferSection n M ordinary underlying U form (P * Q)
  leftScalar : ∀ (U : Opens M) (a : (analyticCoefficients n M).obj (op U))
      (form : (holomorphicOmega (n := n) (M := M) n).val.obj (op U))
      (P : finiteOperatorRing ℂ M (analyticCoefficients n M) U),
    ordinary.actLeft.hom.app (op U)
      (sourceTensorSection ℂ (TopCat.of M) (OrdinaryDXop n M).X ordinary.X U
        (RightDifferentialModules.rightOperatorValue ℂ M (analyticCoefficients n M) U
          (scalarFinite ℂ M (analyticCoefficients n M) U a))
        (transferSection n M ordinary underlying U form P)) =
      transferSection n M ordinary underlying U (a • form) P
  leftCoordinate : ∀ (x : M) (U : Opens M)
      (hU : (U : Set M) ⊆ (chartAt (TemperedDistributionSectionModels.ComplexCoordinates n) x).source)
      (F : VolumeFrameSource n M x U)
      (C : ChartOperatorSource n M (analyticCoefficients n M) (holomorphicChartValue n M)
        false x U hU) (i : Fin n)
      (form : (holomorphicOmega (n := n) (M := M) n).val.obj (op U))
      (P : finiteOperatorRing ℂ M (analyticCoefficients n M) U),
    ordinary.actLeft.hom.app (op U)
      (sourceTensorSection ℂ (TopCat.of M) (OrdinaryDXop n M).X ordinary.X U
        (RightDifferentialModules.rightOperatorValue ℂ M (analyticCoefficients n M) U
          (C.coordinateOperator i)) (transferSection n M ordinary underlying U form P)) =
      transferSection n M ordinary underlying U (-coordinateLie n M x U hU F C i form) P -
        transferSection n M ordinary underlying U form (C.coordinateOperator i * P)
  betaMap : BimoduleMappingSource (IndSheafAlphaBetaModels.beta ℂ (TopCat.of M) CX.alpha CX.beta)
    (OrdinaryDXop n M) (OrdinaryDX n M)

def nativeOmegaTransfer (S : OmegaTransferSource n M) :
    Bimod (betaRing (TopCat.of M) (analyticOppositeDifferentialRing n M))
      (betaRing (TopCat.of M) (analyticDifferentialRing n M)) :=
  S.betaMap.functor.obj S.ordinary

end MathlibExt.AlgebraicGeometry.NativeOmegaTransferModels
