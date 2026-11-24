/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.VonNeumannAlgebra.Basic
public import MathlibExt.Analysis.CStarAlgebra.PositiveFunctionalProjectionResidual

/-!
# The original positive functional's right-projection residual norm bound

The original source-facing name delegates to the generic unital C-star
positive-functional/projection theorem with the actual inherited norm and
canonical coefficient orders. All original functional/projection values
and zero-H cases are unchanged.
The residual value ψ(1-p) controls the continuous-dual norm error used by
finite-projection approximation; no normal membership or cutoff bound is
an input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The literal right-projection residual has its original positive-functional norm bound. -/
theorem positiveFunctional_rightProjection_residual_norm_le (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ) (p : M), IsStarProjection p →
      ‖ψ.toContinuousLinearMap -
        ψ.toContinuousLinearMap.comp ((ContinuousLinearMap.mul ℂ M).flip p)‖ ≤
        Real.sqrt (‖ψ.toContinuousLinearMap‖ * ‖ψ.toContinuousLinearMap (1 - p)‖) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  exact PositiveContinuousLinearMap.rightProjection_residual_norm_le (A := M)

end

end VonNeumannAlgebra
