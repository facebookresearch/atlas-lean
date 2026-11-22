/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# The chain rule for gradients

For `g : E → F` between real Hilbert spaces and `f : F → ℝ`, the gradient of `f ∘ g` is the
adjoint of `g`'s derivative applied to the gradient of `f`:
`∇ (f ∘ g) x = (Dg x)† (∇ f (g x))` (`gradient_comp`). This is the identity behind reverse-mode
differentiation (backpropagation, `CSLibExt/MachineLearning/Backpropagation.lean`).
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt

open InnerProductSpace ContinuousLinearMap
open scoped Gradient

/-- **The chain rule for gradients**: `∇ (f ∘ g) x = (Dg x)† ∇ f (g x)`. -/
theorem gradient_comp {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} {g : E → F} {x : E} (hf : DifferentiableAt ℝ f (g x))
    (hg : DifferentiableAt ℝ g x) :
    ∇ (f ∘ g) x = adjoint (fderiv ℝ g x) (∇ f (g x)) := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, adjoint_inner_left, inner_gradient_left, fderiv_comp x hf hg,
    comp_apply]

end MetaMathlibExt
