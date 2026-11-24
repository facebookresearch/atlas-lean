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

public import MathlibExt.Analysis.VonNeumannAlgebra.LocalizedEvaluationRange
public import Mathlib.Analysis.Real.Sqrt

/-!
# The original localized evaluation-range functional is bounded

The existing squared vector bound implies a norm bound with constant
sqrt(‖ψ(1)‖). Every point of the actual evaluation range has an original
operator preimage, so the same estimate bounds the constructed range
functional. Its continuous linear map and original localized value equation
are constructed without a supplied norm or normality certificate.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The original range factor is bounded, with its norm estimate and literal values proved internally. -/
def localizedEvaluationRangeBoundedFunctional (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    (ψ : PositiveContinuousLinearMap ℂ M ℂ) → (p : M) → IsStarProjection p → (ξ : H) →
      (∀ b : PositiveElement M,
        @LE.le M (CStarAlgebra.spectralOrder M).toLE (b : M) p →
        (ψ.toContinuousLinearMap (b : M)).re ≤ (vectorFunctional M ξ ξ (b : M)).re) →
      {g : StrongDual ℂ (LinearMap.range (localizedOperatorEvaluation M p ξ).toLinearMap) //
        (∀ a : M, g ((localizedOperatorEvaluation M p ξ).toLinearMap.rangeRestrict a) =
          ψ.toContinuousLinearMap (a * p)) ∧
        ∀ x, ‖g x‖ ≤ Real.sqrt ‖ψ.toContinuousLinearMap 1‖ * ‖x‖} := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ p hp ξ hlocal
  let A := (localizedOperatorEvaluation M p ξ).toLinearMap
  let factor := localizedEvaluationRangeFunctional M ψ p hp ξ hlocal
  have hbound (a : M) : ‖ψ.toContinuousLinearMap (a * p)‖ ≤
      Real.sqrt ‖ψ.toContinuousLinearMap 1‖ * ‖A a‖ := by
    have hsquare := localizedPositiveFunctional_norm_sq_le_vector M ψ p hp ξ hlocal a
    change ‖ψ.toContinuousLinearMap (a * p)‖ ^ 2 ≤ ‖ψ.toContinuousLinearMap 1‖ * ‖A a‖ ^ 2
      at hsquare
    have h := Real.sqrt_le_sqrt hsquare
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (norm_nonneg _) _,
      Real.sqrt_sq (norm_nonneg _)] at h
    exact h
  have hfactor (x : LinearMap.range A) : ‖factor.val x‖ ≤
      Real.sqrt ‖ψ.toContinuousLinearMap 1‖ * ‖x‖ := by
    obtain ⟨a, rfl⟩ := A.surjective_rangeRestrict x
    rw [factor.property a]
    exact hbound a
  let g : StrongDual ℂ (LinearMap.range A) :=
    factor.val.mkContinuous (Real.sqrt ‖ψ.toContinuousLinearMap 1‖) hfactor
  refine ⟨g, ?_, ?_⟩
  · intro a
    change factor.val (A.rangeRestrict a) = ψ.toContinuousLinearMap (a * p)
    exact factor.property a
  · intro x
    exact hfactor x

end

end VonNeumannAlgebra
