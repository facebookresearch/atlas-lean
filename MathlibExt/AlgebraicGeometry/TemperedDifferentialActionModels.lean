/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticChartDifferentialOperators
public import MathlibExt.AlgebraicGeometry.SubanalyticIndDistributionModels

/-!
# Actual compact-closure local D actions on the source LF quotients

An operator on U acts only on relatively compact subanalytic V with
closure(V) contained in U. On every original chart test dual the action
is its prescribed full LF formal transpose. The quotient projection is
fixed on every global distribution family. These source constructions
do not grant arbitrary coefficients on all globally extendible Db^t(U).

Source: DK1311.2374v2 Definition5.1.1, Proposition5.1.3, Section5.2;
native LF quotient and operator constructors: Mathlib56a005, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.TemperedDifferentialActionModels

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open TemperedDistributionSectionModels ManifoldDistributionModels
open AnalyticChartDifferentialOperators SubanalyticIndDistributionModels
open DifferentialOperatorSheaves

variable (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (ComplexCoordinates n) M]
  (A : ChartOpenSource n M) (J : TestDensityTransferSource n M A)

def globalChartProjection (x : M) (B : Opens M)
    (hB : (B : Set M) ⊆ (chartAt (ComplexCoordinates n) x).source) :
    ManifoldDistributionModels.GlobalDistribution n M A J →ₗ[ℂ]
      ComplexDistribution (ComplexCoordinates n) (A.coordinateOpen x B hB) where
  toFun T := T.val ⟨(x, B), le_top, hB⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The original native quotient projection on every source chart test dual. -/
structure TemperedChartProjectionSource where
  projection : ∀ (V B : Opens M) (_h : B ≤ V) (x : M)
      (hB : (B : Set M) ⊆ (chartAt (ComplexCoordinates n) x).source),
    ManifoldDistributionModels.TemperedSections n M A J V →ₗ[ℂ]
      ComplexDistribution (ComplexCoordinates n) (A.coordinateOpen x B hB)
  quotientValue : ∀ (V B : Opens M) (h : B ≤ V) (x : M)
      (hB : (B : Set M) ⊆ (chartAt (ComplexCoordinates n) x).source)
      (T : ManifoldDistributionModels.GlobalDistribution n M A J),
    projection V B h x hB (temperedProjection n M A J V T) =
      globalChartProjection n M A J x B hB T

variable (P : TemperedChartProjectionSource n M A J)
  (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} ℂ)
  (value : ∀ U : Opens M, O.obj (op U) → M → ComplexCoordinates n → ℂ) (bar : Bool)

/-- Source construction of all full local operators on the actual globally extendible quotient. -/
structure TemperedOperatorSource where
  chartOperators : ∀ (x : M) (U : Opens M)
      (hU : (U : Set M) ⊆ (chartAt (ComplexCoordinates n) x).source),
    ChartOperatorSource n M O value bar x U hU
  transpose : ∀ (x : M) (U : Opens M)
      (hU : (U : Set M) ⊆ (chartAt (ComplexCoordinates n) x).source)
      (B : Opens M) (hB : B ≤ U),
    LFTransposeSource n M O value bar x U hU (chartOperators x U hU) A B hB
  action : ∀ (U : Opens M) (Q : finiteOperatorRing ℂ M O U)
      (V : RelativelyCompactSubanalyticOpen n M)
      (_hVU : closure (V.openSet : Set M) ⊆ U),
    ManifoldDistributionModels.TemperedSections n M A J V.openSet →ₗ[ℂ]
      ManifoldDistributionModels.TemperedSections n M A J V.openSet
  chartValue : ∀ (U : Opens M) (Q : finiteOperatorRing ℂ M O U)
      (V : RelativelyCompactSubanalyticOpen n M) (hVU : closure (V.openSet : Set M) ⊆ U)
      (x : M) (W : Opens M) (hWU : W ≤ U)
      (hW : (W : Set M) ⊆ (chartAt (ComplexCoordinates n) x).source)
      (B : Opens M) (hBW : B ≤ W) (hBV : B ≤ V.openSet)
      (T : ManifoldDistributionModels.GlobalDistribution n M A J),
    P.projection V.openSet B hBV x (fun y hy => hW (hBW hy))
      (action U Q V hVU (temperedProjection n M A J V.openSet T)) =
        (globalChartProjection n M A J x B (fun y hy => hW (hBW hy)) T).comp
          (MulOpposite.unop ((transpose x W hW B hBW).transpose
            (restrictFinite ℂ M O hWU Q)))

end MathlibExt.AlgebraicGeometry.TemperedDifferentialActionModels
