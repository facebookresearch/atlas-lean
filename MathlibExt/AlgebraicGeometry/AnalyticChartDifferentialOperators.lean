/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeIndDifferentialContexts
public import MathlibExt.AlgebraicGeometry.ManifoldDistributionModels

/-!
# Full chart differential operators and their original LF transpose

The local generators are original finite-order operators, whose function
values are the chart Wirtinger derivatives. Local generation is a genuine
ordinary analytic differential-operator proof request. The LF transpose
is an anti-ring map; its scalar and coordinate values fix all full local
operators through those generators. The tempered action is requested only
on relatively compact V with closure contained in the coefficient open U.

Source: DK1311.2374v2 Sections4.10,5.1,5.2; ordinary local differential
operator calculus. Native finite operators and LF maps: Mathlib56a005,
Apache2.0, with original credits in the imported ports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticChartDifferentialOperators

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open DifferentialOperatorSheaves DifferentialOperatorScalars
open TemperedDistributionSectionModels ManifoldDistributionModels NativeIndDifferentialContexts
open scoped Manifold ContDiff

variable (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (ComplexCoordinates n) M]
  (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} ℂ)

def holomorphicChartValue [IsManifold 𝓘(ℂ, ComplexCoordinates n) ∞ M] (U : Opens M)
    (a : (analyticCoefficients n M).obj (op U))
    (x : M) : ComplexCoordinates n → ℂ :=
  HolomorphicCoefficientSheaves.chartFunction (ComplexCoordinates n) M a.val x

def conjugateChartValue [IsManifold 𝓘(ℂ, ComplexCoordinates n) ∞ M] (U : Opens M)
    (a : (analyticConjugateCoefficients n M).obj (op U))
    (x : M) : ComplexCoordinates n → ℂ :=
  fun z => star (HolomorphicCoefficientSheaves.chartFunction (ComplexCoordinates n) M a.val x z)

def valueWirtinger (bar : Bool) (f : ComplexCoordinates n → ℂ) (z : ComplexCoordinates n)
    (i : Fin n) : ℂ :=
  (1 / 2 : ℂ) * ((fderiv ℝ f z) (realCoordinate n i) +
    (if bar then Complex.I else -Complex.I) * (fderiv ℝ f z) (imaginaryCoordinate n i))

variable (value : ∀ U : Opens M, O.obj (op U) → M → ComplexCoordinates n → ℂ)
  (bar : Bool) (x : M) (U : Opens M)
  (hU : (U : Set M) ⊆ (chartAt (ComplexCoordinates n) x).source)

/-- Full local finite-operator generation, with the actual values on every subopen. -/
structure ChartOperatorSource (_hU : (U : Set M) ⊆ (chartAt (ComplexCoordinates n) x).source) where
  coordinateOperator : Fin n → finiteOperatorRing ℂ M O U
  orderOne : ∀ (i : Fin n) (V : Inside M U),
    MathlibExt.RingTheory.GeometricDifferentialOperators.OrderLE ℂ (O.obj (op V.val)) 1
      ((coordinateOperator i).val.val V)
  derivativeValue : ∀ (i : Fin n) (V : Opens M) (hV : V ≤ U) (a : O.obj (op V))
      (y : V),
    value V ((coordinateOperator i).val.val ⟨V, hV⟩ a) x
        ((chartAt (ComplexCoordinates n) x) y.val) =
      valueWirtinger n bar (value V a x) ((chartAt (ComplexCoordinates n) x) y.val) i
  generation : ∀ P : finiteOperatorRing ℂ M O U,
    P ∈ Subring.closure
      (Set.range (scalarFinite ℂ M O U) ∪ Set.range coordinateOperator)

def testScalar (V : Opens (ComplexCoordinates n)) (c : ℂ) :
    ComplexTest (ComplexCoordinates n) V →L[ℂ] ComplexTest (ComplexCoordinates n) V :=
  TestFunction.postcompCLM (c • ContinuousLinearMap.id ℂ ℂ)

def testWirtinger (bar : Bool) (V : Opens (ComplexCoordinates n)) (i : Fin n) :
    ComplexTest (ComplexCoordinates n) V →L[ℂ] ComplexTest (ComplexCoordinates n) V :=
  let realDerivative : ComplexTest (ComplexCoordinates n) V →L[ℂ]
      ComplexTest (ComplexCoordinates n) V := TestFunction.lineDerivCLM ℂ (realCoordinate n i)
  let imaginaryDerivative : ComplexTest (ComplexCoordinates n) V →L[ℂ]
      ComplexTest (ComplexCoordinates n) V := TestFunction.lineDerivCLM ℂ (imaginaryCoordinate n i)
  (testScalar n V (1 / 2)).comp
    (realDerivative + (testScalar n V (if bar then Complex.I else -Complex.I)).comp
      imaginaryDerivative)

variable (C : ChartOperatorSource n M O value bar x U hU)
  (A : ChartOpenSource n M) (V : Opens M) (hV : V ≤ U)

/-- The full formal transpose is fixed by the original coefficient multiplication and test derivative. -/
structure LFTransposeSource where
  transpose : finiteOperatorRing ℂ M O U →+*
    (ComplexTest (ComplexCoordinates n)
      (A.coordinateOpen x V (fun y hy => hU (hV hy))) →L[ℂ]
        ComplexTest (ComplexCoordinates n)
          (A.coordinateOpen x V (fun y hy => hU (hV hy))))ᵐᵒᵖ
  scalar : ∀ (a : O.obj (op U))
      (φ : ComplexTest (ComplexCoordinates n)
        (A.coordinateOpen x V (fun y hy => hU (hV hy)))) (z : ComplexCoordinates n),
    MulOpposite.unop (transpose (scalarFinite ℂ M O U a)) φ z = value U a x z * φ z
  derivative : ∀ i : Fin n, MulOpposite.unop (transpose (C.coordinateOperator i)) =
    -testWirtinger n bar (A.coordinateOpen x V (fun y hy => hU (hV hy))) i

end MathlibExt.AlgebraicGeometry.AnalyticChartDifferentialOperators
