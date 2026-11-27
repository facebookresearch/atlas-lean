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
# Dual norm error of right projection localization

For a positive bounded functional `ψ` on a concrete von Neumann algebra and star projection `p`,
define `ψ_p(a)=ψ(ap)`. Then `‖ψ-ψ_p‖≤√(‖ψ‖ |ψ(1-p)|)` in the continuous-dual norm.

This estimate requires no normality of `ψ` or local vector domination, and applies to zero
projections and zero algebras.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Norm bound for a positive functional's right-projection residual.** Let `H` be a
complete complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M →
ℂ` be a positive bounded complex-linear functional for the spectral orders. for a star
projection `p∈M` and `ψ_p(a)=ψ(ap)`, `‖ψ-ψ_p‖≤√(‖ψ‖*|ψ(1-p)|)`. -/
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
