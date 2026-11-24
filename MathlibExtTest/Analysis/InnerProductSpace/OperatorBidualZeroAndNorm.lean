/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.InnerProductSpace.OperatorBidual
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Checks of the actual operator-bidual retraction on a complex multiplier
and on the canonical zero-dimensional Hilbert space. -/

noncomputable section
open MathlibExt.Analysis.InnerProductSpace

namespace MathlibExtTest.OperatorBidualZeroAndNorm

example :
    operatorBidualRetraction
      (NormedSpace.inclusionInDoubleDual ℂ (ℂ →L[ℂ] ℂ)
        (Complex.I • ContinuousLinearMap.id ℂ ℂ)) 1 = Complex.I := by
  simp

example :
    ‖operatorBidualRetraction
      (NormedSpace.inclusionInDoubleDual ℂ (ℂ →L[ℂ] ℂ)
        (Complex.I • ContinuousLinearMap.id ℂ ℂ))‖ = 1 := by
  simp [norm_smul]

example (Φ : StrongDual ℂ (StrongDual ℂ
    (EuclideanSpace ℂ (Fin 0) →L[ℂ] EuclideanSpace ℂ (Fin 0)))) :
    ‖operatorBidualRetraction Φ‖ = 0 := by
  have h : operatorBidualRetraction Φ = 0 := Subsingleton.elim _ _
  rw [h, norm_zero]

end MathlibExtTest.OperatorBidualZeroAndNorm
