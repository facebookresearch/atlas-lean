/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.ZMod.Basic

import Mathlib.Logic.Equiv.Basic

/-!
# Circular convolution equivariance

Signals are functions on `ZMod n` with `n` nonzero. Circular convolution uses
`(k ⋆ x) i = ∑ j, k j * x (i - j)`, and shifting a signal uses
`(shift s x) i = x (i - s)`. With these matched conventions, circular
convolution commutes with cyclic shifts, and the same holds after a shared
pointwise activation or after composing two such layers.

## Main declarations

* `shift`: cyclically shifted signal.
* `circConv`: circular convolution.
* `convLayer`: circular convolution followed by a pointwise activation.
* `circConv_shift`, `convLayer_shift`, `convLayer_comp_shift`: equivariance.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Convolution

/-- Shift a signal on `ZMod n` by `s`: `(shift s x) i = x (i - s)`. -/
def shift {n : ℕ} (s : ZMod n) (x : ZMod n → ℝ) : ZMod n → ℝ :=
  fun i => x (i - s)

/-- Circular convolution on `ZMod n`, with the mathematical convolution
convention `(k ⋆ x) i = ∑ j, k j * x (i - j)`. -/
noncomputable def circConv {n : ℕ} [NeZero n] (k x : ZMod n → ℝ) :
    ZMod n → ℝ :=
  fun i => ∑ j, k j * x (i - j)

/-- One circular-convolution layer with a shared pointwise activation. -/
noncomputable def convLayer {n : ℕ} [NeZero n] (σ : ℝ → ℝ)
    (k x : ZMod n → ℝ) : ZMod n → ℝ :=
  fun i => σ (circConv k x i)

/-- Circular convolution commutes with cyclic shifts. -/
theorem circConv_shift {n : ℕ} [NeZero n] (k x : ZMod n → ℝ) (s : ZMod n) :
    circConv k (shift s x) = shift s (circConv k x) := by
  funext i
  simp only [circConv, shift]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  congr 1
  exact sub_right_comm i j s

/-- A pointwise activation after circular convolution preserves cyclic-shift
equivariance. -/
theorem convLayer_shift {n : ℕ} [NeZero n] (σ : ℝ → ℝ)
    (k x : ZMod n → ℝ) (s : ZMod n) :
    convLayer σ k (shift s x) = shift s (convLayer σ k x) := by
  have h := circConv_shift k x s
  funext i
  simp only [convLayer]
  rw [h]
  simp only [shift, convLayer]

/-- A composition of two circular-convolution layers is cyclic-shift
equivariant. -/
theorem convLayer_comp_shift {n : ℕ} [NeZero n] (σ₁ σ₂ : ℝ → ℝ)
    (k₁ k₂ x : ZMod n → ℝ) (s : ZMod n) :
    convLayer σ₂ k₂ (convLayer σ₁ k₁ (shift s x)) =
      shift s (convLayer σ₂ k₂ (convLayer σ₁ k₁ x)) := by
  rw [convLayer_shift, convLayer_shift]

end Cslib.MachineLearning.Convolution
