/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AlgebraicMovingEulerModels
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Nonreduced coefficient and physical dual-weight checks

The differential calculation uses a genuine nonzero nilpotent scheme
coefficient. The Euler sign check starts with cotangent weight minus
one and computes the leading class of its physical tangent dual.
-/

set_option autoImplicit false
@[expose] noncomputable section
namespace MathlibExtTest.AlgebraicGeometry.EquivariantVirtualLocalization

open MathlibExt.AlgebraicGeometry
open AlgebraicWeightBundleModels AlgebraicMovingEulerModels IntegralChowChernModels

def epsilon : TrivSqZeroExt ℂ ℂ := TrivSqZeroExt.inr 1

example : epsilon * epsilon = 0 := TrivSqZeroExt.inr_mul_inr ℂ (1 : ℂ) 1

example : epsilon ≠ 0 := by
  intro h
  have h' : (1 : ℂ) = 0 :=
    TrivSqZeroExt.inr_injective (R := ℂ) (by simpa [epsilon] using h)
  exact one_ne_zero h'

example :
    KaehlerDifferential.D (TrivSqZeroExt ℂ ℂ) (Polynomial (TrivSqZeroExt ℂ ℂ))
        (Polynomial.C (1+epsilon) * Polynomial.X) =
      (1+epsilon) • KaehlerDifferential.D (TrivSqZeroExt ℂ ℂ)
        (Polynomial (TrivSqZeroExt ℂ ℂ)) Polynomial.X :=
  weightOneCoordinateDifferential (TrivSqZeroExt ℂ ℂ) (1+epsilon)

/-- A cotangent character of weight minus one has tangent-dual Euler leading term plus t. -/
example (F : SchemeData) (E : DualMovingSummand F)
    (rank : E.rank=1) (cotangentWeight : E.integer.weight = -1) :
    leadingCoefficient F [E] = LaurentPolynomial.T 1 := by
  simp [leadingCoefficient, movingRank, rank, cotangentWeight]

end MathlibExtTest.AlgebraicGeometry.EquivariantVirtualLocalization
