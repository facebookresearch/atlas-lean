/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Amplification norm factories at zero coefficients and empty Hilbert indices. -/
noncomputable section
universe uH uA
open CStarModule.HilbertAmplification
variable (H : Type uH) (A : Type uA)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NonUnitalCStarAlgebra A]
local instance : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A

example [Subsingleton A] (ξ : H) (a : A) : ‖pure H A ξ a‖ = 0 := by
  have ha : a = 0 := Subsingleton.elim _ _
  simpa only [ha, norm_zero, mul_zero] using norm_pure H A ξ a

example (a : A) :
    ‖pure (EuclideanSpace ℂ (Fin 0)) A 0 a‖ = 0 := by
  simpa only [norm_zero, zero_mul] using
    norm_pure (EuclideanSpace ℂ (Fin 0)) A 0 a

example (a : A) : ‖pure ℂ A Complex.I a‖ = ‖a‖ := by
  simpa using norm_pure ℂ A Complex.I a
end
