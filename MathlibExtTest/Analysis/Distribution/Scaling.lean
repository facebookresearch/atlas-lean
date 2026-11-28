/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Distribution.Scaling
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.NormNum

/-! # Nonzero smooth test-function consumers of affine pullback and scaling -/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Distributions

namespace MathlibExtTest.Analysis.Distribution.Scaling

-- Use the stock smooth bump with inner radius 1 and outer radius 2.
private def unitBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := zero_lt_one
  rIn_lt_rOut := one_lt_two

private def bumpTest : 𝓓((⊤ : Opens ℝ), ℝ) where
  toFun := unitBump
  contDiff' := unitBump.contDiff
  hasCompactSupport' := unitBump.hasCompactSupport
  tsupport_subset' := Set.subset_univ _

private def reflection : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.neg ℝ

private theorem bumpTest_zero : bumpTest 0 = 1 := by
  change unitBump 0 = 1
  exact unitBump.one_of_mem_closedBall
    (Metric.mem_closedBall_self unitBump.rIn_pos.le)

private theorem bumpTest_boundary : bumpTest 2 = 0 := by
  change unitBump 2 = 0
  exact unitBump.zero_of_le_dist (by norm_num [unitBump, Real.dist_eq])

private theorem bumpTest_tsupport :
    tsupport bumpTest = Metric.closedBall (0 : ℝ) 2 := by
  change tsupport (unitBump : ℝ → ℝ) = Metric.closedBall (0 : ℝ) unitBump.rOut
  exact unitBump.tsupport_eq

example : ContDiff ℝ ∞ bumpTest ∧ HasCompactSupport bumpTest :=
  ⟨bumpTest.contDiff, bumpTest.hasCompactSupport⟩

example : bumpTest ≠ 0 := by
  intro h
  have h0 := congrArg (fun f : 𝓓((⊤ : Opens ℝ), ℝ) => f 0) h
  simpa [bumpTest_zero] using h0

-- Vanishing at the outer boundary does not remove that point from closed support.
example : bumpTest 2 = 0 ∧ (2 : ℝ) ∈ tsupport bumpTest := by
  refine ⟨bumpTest_boundary, ?_⟩
  rw [bumpTest_tsupport]
  norm_num [Metric.mem_closedBall, Real.dist_eq]

-- The affine map is x ↦ -x + 2, so the nonzero center moves from 0 to 2.
example : TestFunction.affinePrecompCLM reflection 2 bumpTest 2 = 1 := by
  simp [reflection, bumpTest_zero]

example : TestFunction.affineScaleCLM (-2) reflection 2 bumpTest 2 = -2 := by
  simp [reflection, bumpTest_zero, smul_eq_mul]

example : TestFunction.affineScaleCLM (-2) reflection 2 bumpTest ≠ 0 := by
  intro h
  have h2 := congrArg (fun f : 𝓓((⊤ : Opens ℝ), ℝ) => f 2) h
  norm_num [reflection, bumpTest_zero, smul_eq_mul] at h2

example :
    TestFunction.affineScaleCLM (-2) reflection 2 (bumpTest + bumpTest) =
      TestFunction.affineScaleCLM (-2) reflection 2 bumpTest +
        TestFunction.affineScaleCLM (-2) reflection 2 bumpTest :=
  (TestFunction.affineScaleCLM (-2) reflection 2).map_add bumpTest bumpTest

example : TestFunction.affineScaleCLM (-2) reflection 2 (bumpTest + bumpTest) 2 = -4 := by
  norm_num [reflection, bumpTest_zero, smul_eq_mul]

example :
    tsupport (TestFunction.affinePrecompCLM reflection 2 bumpTest) =
      {x : ℝ | -x + 2 ∈ Metric.closedBall (0 : ℝ) 2} := by
  ext x
  simp [TestFunction.tsupport_affinePrecompCLM, bumpTest_tsupport, reflection]

-- The reflected boundary is 0: evaluation is zero, but the point is in closed support.
example :
    TestFunction.affinePrecompCLM reflection 2 bumpTest 0 = 0 ∧
      (0 : ℝ) ∈ tsupport (TestFunction.affinePrecompCLM reflection 2 bumpTest) := by
  constructor
  · simp [reflection, bumpTest_boundary]
  · rw [TestFunction.tsupport_affinePrecompCLM]
    change reflection 0 + 2 ∈ tsupport bumpTest
    rw [bumpTest_tsupport]
    norm_num [reflection, Metric.mem_closedBall, Real.dist_eq]

example :
    TestFunction.affinePrecompCLM reflection.symm (-reflection.symm 2)
      (TestFunction.affinePrecompCLM reflection 2 bumpTest) = bumpTest :=
  TestFunction.affinePrecompCLM_inverse reflection 2 bumpTest

-- Exercise the actual fixed-support space and its compact preimage as well.
private def supportCompact : Compacts ℝ := ⟨tsupport bumpTest, bumpTest.hasCompactSupport⟩

private def supportedBump : ContDiffMapSupportedIn ℝ ℝ ⊤ supportCompact :=
  .of_support_subset bumpTest.contDiff (subset_tsupport bumpTest)

example :
    ContDiffMapSupportedIn.affinePrecompCLM reflection 2 supportCompact supportedBump 2 = 1 := by
  change bumpTest (reflection 2 + 2) = 1
  simp [reflection, bumpTest_zero]

example : (0 : ℝ) ∈ TestFunction.affinePullbackCompact reflection 2 supportCompact := by
  rw [TestFunction.mem_affinePullbackCompact]
  change reflection 0 + 2 ∈ tsupport bumpTest
  rw [bumpTest_tsupport]
  norm_num [reflection, Metric.mem_closedBall, Real.dist_eq]

-- Here c is the output scalar, and c = 0 annihilates a genuinely nonzero pullback.
private theorem zero_scale :
    TestFunction.affineScaleCLM 0 reflection 2 bumpTest = 0 := by
  ext x
  simp

example : tsupport (TestFunction.affineScaleCLM 0 reflection 2 bumpTest) = ∅ := by
  rw [zero_scale]
  simp

example :
    tsupport (TestFunction.affineScaleCLM 0 reflection 2 bumpTest) ⊆
      (TestFunction.affineHomeomorph reflection 2) ⁻¹' tsupport bumpTest :=
  TestFunction.tsupport_affineScaleCLM_subset 0 reflection 2 bumpTest

-- The affine preimage still contains the moved center when the scaled support is empty.
example :
    (2 : ℝ) ∈ (TestFunction.affineHomeomorph reflection 2) ⁻¹' tsupport bumpTest ∧
      (2 : ℝ) ∉ tsupport (TestFunction.affineScaleCLM 0 reflection 2 bumpTest) := by
  constructor
  · change reflection 2 + 2 ∈ tsupport bumpTest
    rw [bumpTest_tsupport]
    norm_num [reflection, Metric.mem_closedBall, Real.dist_eq]
  · rw [zero_scale]
    simp

end MathlibExtTest.Analysis.Distribution.Scaling
