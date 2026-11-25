/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.TwoChartIntegralModel

@[expose] public section

open AlgebraicCurve AlgebraicGeometry CategoryTheory

/-- Unfolding and characterization on the concrete `ℤ ⊂ ℚ`, `j = 2` model. -/
example [Fact ((2 : ℚ) ≠ 0)] : (2 : ℚ) ∈ TwoChartIntegralModel.chartAlgFin ℤ ℚ 2 ∧
    TwoChartIntegralModel.chartFinOpen ℤ ℚ 2 ⊔
      TwoChartIntegralModel.chartInfOpen ℤ ℚ 2 = ⊤ ∧
    (TwoChartIntegralModel.polynomialToChartFin ℤ ℚ 2 Polynomial.X : ℚ) = 2 := by
  refine ⟨TwoChartIntegralModel.subset_chartAlg ℤ ℚ _ rfl,
    TwoChartIntegralModel.twoChartCover ℤ ℚ 2, ?_⟩
  rw [TwoChartIntegralModel.polynomialToChartFin_X,
    TwoChartIntegralModel.coe_jChartFin]

/-- The gluing condition for the concrete glued scheme at `j = 2`. -/
example [Fact ((2 : ℚ) ≠ 0)] : TwoChartIntegralModel.fFin ℤ ℚ 2 ≫ TwoChartIntegralModel.ιFin ℤ ℚ 2 =
    TwoChartIntegralModel.fInf ℤ ℚ 2 ≫ TwoChartIntegralModel.ιInf ℤ ℚ 2 := by
  exact TwoChartIntegralModel.glue_condition ℤ ℚ 2

/-- The chart algebra is Mathlib's integral closure of `ℤ[S]` in `ℚ`, up to reducible unfolding. -/
example (S : Set ℚ) :
    TwoChartIntegralModel.chartAlg ℤ ℚ S =
      (integralClosure (Algebra.adjoin ℤ S) ℚ).restrictScalars ℤ := by
  with_reducible rfl

/-- The reduction of the concrete model modulo `2` lies over `Spec (ℤ ⧸ (2))`. -/
example [Fact ((2 : ℚ) ≠ 0)] :
    TwoChartIntegralModel.reductionι ℤ ℚ 2 (Ideal.span {2}) ≫ TwoChartIntegralModel.toBase ℤ ℚ 2 =
      TwoChartIntegralModel.reductionToBase ℤ ℚ 2 (Ideal.span {2}) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {2}))) :=
  TwoChartIntegralModel.reductionι_toBase ℤ ℚ 2 _
