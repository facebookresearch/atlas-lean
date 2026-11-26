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
# Linear functional on a localized vector evaluation range

Suppose positive `ψ`, star projection `p` and vector `ξ` satisfy `Re ψ(b)≤Re ⟨ξ,bξ⟩` for
`0≤b≤p`. On the linear subspace `V={ (ap)ξ : a∈M } ⊆ H`, the formula `g((ap)ξ)=ψ(ap)` is
well-defined and complex-linear.

The kernel inclusion of the evaluation and localized functional gives this factorization. No
continuity or norm estimate is assumed for the range functional in this construction.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Linear factor through the localized evaluation range.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a positive
bounded complex-linear functional for the spectral orders. Let `p ∈ M` be a star
projection and `ξ ∈ H` satisfy `Re ψ(b)≤Re ⟨ξ,bξ⟩` for every positive `b≤p`. for
`V=range(a ↦ (ap)ξ) ⊆ H`, the construction returns `g : V →ₗ[ℂ] ℂ` with `g((ap)ξ)=ψ(ap)`
for every `a∈M`. -/
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
