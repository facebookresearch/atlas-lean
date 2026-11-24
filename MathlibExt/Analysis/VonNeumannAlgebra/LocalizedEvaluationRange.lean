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

public import MathlibExt.Analysis.VonNeumannAlgebra.LocalizedEvaluationKernel

/-!
# Factor the original localized functional through the actual evaluation range

The original local comparison proves the evaluation-kernel inclusion. The
stock surjective-range factorization then constructs a linear functional on
the actual range of a ↦ (a*p)ξ, with literal value ψ(a*p). The value equation
is proved by the stock lift law, rather than supplied as a constructor field.
No norm or normal-functional membership certificate is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual range functional, with its original localized value equation proved internally. -/
def localizedEvaluationRangeFunctional (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    (ψ : PositiveContinuousLinearMap ℂ M ℂ) → (p : M) → IsStarProjection p → (ξ : H) →
      (∀ b : PositiveElement M,
        @LE.le M (CStarAlgebra.spectralOrder M).toLE (b : M) p →
        (ψ.toContinuousLinearMap (b : M)).re ≤ (vectorFunctional M ξ ξ (b : M)).re) →
      {g : LinearMap.range (localizedOperatorEvaluation M p ξ).toLinearMap →ₗ[ℂ] ℂ //
        ∀ a : M, g ((localizedOperatorEvaluation M p ξ).toLinearMap.rangeRestrict a) =
          ψ.toContinuousLinearMap (a * p)} := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ p hp ξ hlocal
  let A := (localizedOperatorEvaluation M p ξ).toLinearMap
  let ρ := (localizedFunctionalLinearMap M ψ.toContinuousLinearMap p).toLinearMap
  have hker : LinearMap.ker A.rangeRestrict ≤ LinearMap.ker ρ := by
    rw [LinearMap.ker_rangeRestrict]
    exact localizedOperatorEvaluation_ker_le M ψ p hp ξ hlocal
  let g : LinearMap.range A →ₗ[ℂ] ℂ :=
    (A.rangeRestrict.liftOfSurjective A.surjective_rangeRestrict) ⟨ρ, hker⟩
  refine ⟨g, ?_⟩
  intro a
  change (A.rangeRestrict.liftOfSurjective A.surjective_rangeRestrict)
    ⟨ρ, hker⟩ (A.rangeRestrict a) = ρ a
  exact LinearMap.equivOfSurjective_apply A.surjective_rangeRestrict hker

end

end VonNeumannAlgebra
