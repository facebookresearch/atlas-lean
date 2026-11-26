/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.PureCrossNorm

/-! Canonical tensor-completion norms with degenerate coefficients or compact factors. -/
noncomputable section
universe uH uA
open scoped TensorProduct
open CStarModule.HilbertAmplification
variable (H : Type uH) (A : Type uA)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NonUnitalCStarAlgebra A]
local instance : NonUnitalCStarAlgebra (CompactTensorCompletion H A) :=
  compactTensorCompletionCStarAlgebra H A

example [Subsingleton A] (a : A)
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    ‖toCompactTensorCompletion H A (a ⊗ₜ[ℂ] T)‖ = 0 := by
  have ha : a = 0 := Subsingleton.elim _ _
  simpa only [ha, norm_zero, zero_mul] using
    norm_toCompactTensorCompletion_tmul H A a T

example (a : A) :
    ‖toCompactTensorCompletion H A
      (a ⊗ₜ[ℂ] (0 : (compactEndomorphismClosedStarIdeal (H := H)).carrier))‖ = 0 := by
  simpa only [norm_zero, mul_zero] using
    norm_toCompactTensorCompletion_tmul H A a
      (0 : (compactEndomorphismClosedStarIdeal (H := H)).carrier)
end
