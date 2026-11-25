/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.Basic

/-! A nonreal pure inner product through the public completed-module factories. -/
noncomputable section
universe uH uA
open CStarModule.HilbertAmplification
variable (H : Type uH) (A : Type uA)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NonUnitalCStarAlgebra A]
local instance : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
local instance : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
local instance : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
local instance : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
local instance : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
local instance : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A

example (a : A) :
    CStarModule.rightInner (B := A) (pure ℂ A 1 a) (pure ℂ A Complex.I a) =
      Complex.I • (star a * a) := by
  simpa using rightInner_pure ℂ A (1 : ℂ) Complex.I a a
end
