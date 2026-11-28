/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.VariableChangeComparison
import Mathlib.Algebra.Order.Field.Rat

open Polynomial WeierstrassCurve

open scoped Polynomial.Bivariate

#check @WeierstrassCurve.mk_evalEval_baseChange
#check @WeierstrassCurve.Affine.CoordinateRing.eq_variableChange_of_equation

/-- The coordinate functions `x, y` of `A_W` satisfy the equation of `W` in `A_W`. -/
theorem equation_coordinates {F : Type*} [Field F] (W : WeierstrassCurve F) :
    (W.baseChange W.toAffine.CoordinateRing).toAffine.Equation
      (algebraMap F _ ((1 : Fˣ) : F) * Affine.CoordinateRing.mk W.toAffine (C X) +
        algebraMap F _ 0)
      (algebraMap F _ ((1 : Fˣ) : F) * Affine.CoordinateRing.mk W.toAffine Y +
        algebraMap F _ 0 * Affine.CoordinateRing.mk W.toAffine (C X) + algebraMap F _ 0) := by
  simp only [Units.val_one, map_one, one_mul, map_zero, add_zero, zero_mul]
  rw [Affine.Equation, mk_evalEval_baseChange]
  have : (W.map (Polynomial.C.comp Polynomial.C)).toAffine.polynomial.evalEval (C X) Y =
      W.toAffine.polynomial := by
    rw [Affine.evalEval_polynomial, Affine.polynomial]
    simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, RingHom.coe_comp, Function.comp_apply,
      map_add, map_mul, map_pow]
    ring
  rw [this]
  exact AdjoinRoot.mk_self

/-- Concrete instance over `ℚ`: the curve `y² + y = x³ - x` compared with itself through the
identity coordinates gives the trivial variable change. -/
example : ((1 : ℚˣ) : ℚ) ^ 2 = ((1 : ℚˣ) : ℚ) ^ 3 ∧
    (((1 : ℚˣ) * (1 : ℚˣ)⁻¹ : ℚˣ) : ℚ) ^ 2 = ((1 : ℚˣ) : ℚ) ∧
    (((1 : ℚˣ) * (1 : ℚˣ)⁻¹ : ℚˣ) : ℚ) ^ 3 = ((1 : ℚˣ) : ℚ) ∧
    (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℚ) =
      (⟨(1 : ℚˣ) * (1 : ℚˣ)⁻¹, 0, 0 / ((1 : ℚˣ) : ℚ), 0⟩ : VariableChange ℚ) •
        (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℚ) :=
  Affine.CoordinateRing.eq_variableChange_of_equation _ _ 1 1 0 0 0
    (equation_coordinates _)
