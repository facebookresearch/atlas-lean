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

public import MathlibExt.Analysis.VonNeumannAlgebra.LocalizedVectorRealization

/-!
# Normality of projection-localized positive functionals

Suppose a positive bounded functional `ψ` is dominated by the vector coefficient of `ξ` on the
positive interval below a star projection `p`. The localization `a ↦ ψ(ap)` is a normal
functional in `M_*`.

Its representing vector identity `ψ(ap)=⟨η,apξ⟩` identifies it with the vector functional `a ↦
⟨η,a(pξ)⟩`. Global normality of `ψ` is not required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Normal-functional member of a projection localization.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a positive
bounded complex-linear functional for the spectral orders. Let `p ∈ M` be a star
projection and `ξ ∈ H` satisfy `Re ψ(b)≤Re ⟨ξ,bξ⟩` for every positive `b≤p`.
`localizedNormalFunctional M ψ p ξ` returns `ρ∈M_*` with `ρ(a)=ψ(ap)` for every `a∈M`. -/
def localizedNormalFunctional (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    (ψ : PositiveContinuousLinearMap ℂ M ℂ) → (p : M) → IsStarProjection p → (ξ : H) →
      (∀ b : PositiveElement M,
        @LE.le M (CStarAlgebra.spectralOrder M).toLE (b : M) p →
        (ψ.toContinuousLinearMap (b : M)).re ≤ (vectorFunctional M ξ ξ (b : M)).re) →
      {ρ : normalFunctionalSpace M // ∀ a : M,
        (ρ.val : StrongDual ℂ M) a = ψ.toContinuousLinearMap (a * p)} := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ p hp ξ hlocal
  let η := localizedFunctionalVector M ψ p hp ξ hlocal
  let ω : H := (p : H →L[ℂ] H) ξ
  let ρ : normalFunctionalSpace M :=
    ⟨vectorFunctional M η.val ω, vectorFunctional_mem_normalFunctionalSpace M η.val ω⟩
  refine ⟨ρ, ?_⟩
  intro a
  change vectorFunctional M η.val ω a = ψ.toContinuousLinearMap (a * p)
  rw [vectorFunctional_apply, η.property a]
  have hproduct : ((a * p : M) : H →L[ℂ] H) ξ = (a : H →L[ℂ] H) ω := by
    change ((a : H →L[ℂ] H) * (p : H →L[ℂ] H)) ξ = _
    rw [mul_apply_eq_comp]
  rw [hproduct]

end

end VonNeumannAlgebra
