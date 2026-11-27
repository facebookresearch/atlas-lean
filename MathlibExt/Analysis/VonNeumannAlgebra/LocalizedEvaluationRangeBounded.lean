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
# Bounded functional on a localized vector evaluation range

Under local domination of a positive functional `ψ` by a vector coefficient below the star
projection `p`, the functional on `V={ (ap)ξ : a∈M }` satisfies `g((ap)ξ)=ψ(ap)` and
`|g(v)|≤√(|ψ(1)|)‖v‖`.

It therefore defines a continuous complex-linear functional on `V` with its inherited Hilbert
norm. Completeness of this range subspace is not required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Bounded range factor with an explicit scalar constant.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a positive
bounded complex-linear functional for the spectral orders. Let `p ∈ M` be a star
projection and `ξ ∈ H` satisfy `Re ψ(b)≤Re ⟨ξ,bξ⟩` for every positive `b≤p`. on `V=range(a
↦ (ap)ξ)`, the construction returns `g∈V*` with `g((ap)ξ)=ψ(ap)` and
`|g(v)|≤√(|ψ(1)|)*‖v‖` for every `v∈V`. -/
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
