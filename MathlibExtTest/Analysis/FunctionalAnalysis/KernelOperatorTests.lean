/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.KernelOperator

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.KernelOperatorTest

open MathlibExt.Analysis.FunctionalAnalysis.KernelOperator

open scoped BoundedContinuousFunction

/-- The kernel operator with kernel `0` is `0`. -/
example : kernelOperator 0 = (0 : KernelSpace →L[ℝ] KernelSpace) :=
  kernelOperator_zero

/-- The kernel operator is additive in the kernel, on the zero kernel. -/
example (k : KernelType) : kernelOperator (k + 0) = kernelOperator k := by
  rw [kernelOperator_add, kernelOperator_zero, add_zero]

/-- The kernel operator is homogeneous in the kernel: scaling the kernel
by `2` scales the operator by `2`. -/
example (k : KernelType) : kernelOperator ((2 : ℝ) • k) = (2 : ℝ) • kernelOperator k :=
  kernelOperator_smul 2 k

/-- Operator-norm bound: `‖kernelOperator k‖ ≤ ‖k‖`. -/
example (k : KernelType) : ‖kernelOperator k‖ ≤ ‖k‖ :=
  norm_kernelOperator_le k

/-- Every kernel operator on `C([0, 1], ℝ)` is compact. -/
example (k : KernelType) : IsCompactOperator (kernelOperator k) :=
  isCompactOperator_kernelOperator k

/-- Constant kernel `1` applied to the constant function `1` gives `1`,
everywhere: `∫₀¹ 1 * 1 = 1`. -/
example (x : Set.Icc (0 : ℝ) 1) :
    kernelOperator (BoundedContinuousFunction.const _ (1 : ℝ))
        (BoundedContinuousFunction.const _ (1 : ℝ)) x = 1 := by
  rw [kernelOperator_apply]
  simp only [kernelIntegrand, kernelExtend, BoundedContinuousFunction.const_apply, one_mul]
  rw [intervalIntegral.integral_const]
  simp

/-- Constant kernel `c` applied to the constant function `1` gives `c`,
everywhere: `∫₀¹ c * 1 = c`. -/
example (c : ℝ) (x : Set.Icc (0 : ℝ) 1) :
    kernelOperator (BoundedContinuousFunction.const _ c)
        (BoundedContinuousFunction.const _ (1 : ℝ)) x = c := by
  rw [kernelOperator_apply]
  simp only [kernelIntegrand, kernelExtend, BoundedContinuousFunction.const_apply, mul_one]
  rw [intervalIntegral.integral_const]
  simp

/-- A constant kernel is separable (with the single pair `φ = 1`, `ψ = c`),
hence its operator has finite rank. -/
example (c : ℝ) : FiniteDimensional ℝ ↥(LinearMap.range
    (kernelOperator (BoundedContinuousFunction.const _ c) :
      KernelSpace →ₗ[ℝ] KernelSpace)) := by
  apply finiteDimensional_range_kernelOperator_of_separable
    (s := {0}) (φ := fun _ => BoundedContinuousFunction.const _ (1 : ℝ))
    (ψ := fun _ => BoundedContinuousFunction.const _ c)
  intro x y
  simp

end MathlibExt.Analysis.FunctionalAnalysis.KernelOperatorTest
