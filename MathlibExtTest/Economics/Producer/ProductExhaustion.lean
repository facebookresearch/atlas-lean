/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Producer.ProductExhaustion
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

open Filter Topology

/-! Tests for `MathlibExt.Economics.Producer.ProductExhaustion`: concrete instances with exact values. -/

namespace MathlibExtTest.Economics.Producer.ProductExhaustion

open _root_.Economics.Producer

/-!
## Test: concrete constant-returns example on `Fin 2`

Production function `f x = 2 * x 0 + 3 * x 1`, input bundle `x = ![1, 2]`,
output price `P = 1`, competitive payments `w = ![2, 3]`, total `8`.
-/

noncomputable def testLin : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
  ((2 : ℝ) • LinearMap.proj 0 + (3 : ℝ) • LinearMap.proj 1 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ)

noncomputable def testL : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap testLin

noncomputable def testF : (Fin 2 → ℝ) → ℝ := ⇑testL

theorem test_hasFDerivAt : HasFDerivAt testF testL ![1, 2] := testL.hasFDerivAt

theorem test_constantReturns :
    ∀ t : ℝ, 0 < t → testF (t • ![1, 2]) = t * testF ![1, 2] := by
  intro t _
  show testL (t • ![1, 2]) = t * testL ![1, 2]
  rw [map_smul, smul_eq_mul]

theorem test_value : testF ![1, 2] = 8 := by
  show testL ![1, 2] = 8
  simp [testL, testLin]
  norm_num

theorem test_euler : testL ![1, 2] = testF ![1, 2] :=
  fderiv_apply_self_eq_of_constantReturns test_hasFDerivAt test_constantReturns

theorem test_marginal_zero : testL (Pi.single 0 1) = 2 := by
  simp [testL, testLin]

theorem test_marginal_one : testL (Pi.single 1 1) = 3 := by
  simp [testL, testLin]

theorem test_marginal_sum :
    ∑ i, testL (Pi.single i 1) * ![1, 2] i = testF ![1, 2] :=
  sum_marginalProduct_mul_eq test_hasFDerivAt test_constantReturns

theorem test_marginal_sum_value : ∑ i, testL (Pi.single i 1) * ![1, 2] i = 8 := by
  rw [test_marginal_sum, test_value]

theorem test_payments : ∀ i : Fin 2, ![2, 3] i = (1:ℝ) * testL (Pi.single i 1) := by
  intro i
  fin_cases i
  · simp [test_marginal_zero]
  · simp [test_marginal_one]

theorem test_exhaustion : ![2, 3] ⬝ᵥ ![1, 2] = (1:ℝ) * testF ![1, 2] :=
  dotProduct_eq_mul_of_competitive_payments test_hasFDerivAt test_constantReturns test_payments

theorem test_total : ![2, 3] ⬝ᵥ ![1, 2] = (8:ℝ) := by
  rw [test_exhaustion, test_value, one_mul]

end MathlibExtTest.Economics.Producer.ProductExhaustion
