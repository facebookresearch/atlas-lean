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
# The original localized functional is an actual normal vector functional

The constructed Riesz vector η represents ψ(a*p) at (a*p)ξ. The original
operator product rewrites this as the vector coefficient at a of η and pξ.
That coefficient belongs to the existing closed normal-functional span.
The resulting normal-functional data have the original localized values;
no normal membership, vector witness or norm certificate is supplied.

This is a local constructor. The global order-normal criterion and the
computed normal GNS homomorphism require separate remaining prerequisites.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Construct the original localized functional in the actual normal-functional space. -/
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
