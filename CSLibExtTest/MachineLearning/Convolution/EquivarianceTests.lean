/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Convolution.Equivariance

@[expose] public section

/-!
# Tests for circular convolution equivariance
-/

set_option autoImplicit false

open Cslib.MachineLearning.Convolution

namespace CSLibExtTest.MachineLearning.Convolution.EquivarianceTests

/-- Shifting by zero is the identity. -/
example {n : ℕ} (x : ZMod n → ℝ) : shift 0 x = x := by
  funext i
  simp [shift]

/-- Circular-convolution equivariance instantiated on `ZMod 3`. -/
example (k x : ZMod 3 → ℝ) (s : ZMod 3) :
    circConv k (shift s x) = shift s (circConv k x) :=
  circConv_shift k x s

/-- One-layer equivariance instantiated on `ZMod 3`. -/
example (σ : ℝ → ℝ) (k x : ZMod 3 → ℝ) (s : ZMod 3) :
    convLayer σ k (shift s x) = shift s (convLayer σ k x) :=
  convLayer_shift σ k x s

/-- Two-layer equivariance instantiated on `ZMod 3`. -/
example (σ₁ σ₂ : ℝ → ℝ) (k₁ k₂ x : ZMod 3 → ℝ) (s : ZMod 3) :
    convLayer σ₂ k₂ (convLayer σ₁ k₁ (shift s x)) =
      shift s (convLayer σ₂ k₂ (convLayer σ₁ k₁ x)) :=
  convLayer_comp_shift σ₁ σ₂ k₁ k₂ x s

/-- With the identity activation, a convolution layer is circular convolution. -/
example {n : ℕ} [NeZero n] (k x : ZMod n → ℝ) :
    convLayer id k x = circConv k x := rfl

end CSLibExtTest.MachineLearning.Convolution.EquivarianceTests
