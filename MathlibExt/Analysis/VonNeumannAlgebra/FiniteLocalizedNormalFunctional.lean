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

public import MathlibExt.Analysis.VonNeumannAlgebra.LocalizedNormalFunctional

/-!
# Finite original projection localizations give an actual normal functional

For each original projection and vector with the literal positive local
comparison, the strict local constructor supplies ψ(·p) in the existing
normal-functional space. Their finite sum is an actual member of the same
space and evaluates to ψ(a*∑p). No normal member or finite-cutoff norm
certificate is an input. Orthogonality and maximal-family approximation
are separate remaining prerequisites for the global normality criterion.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight
open scoped BigOperators

namespace VonNeumannAlgebra

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Construct the finite sum of actual local normal functionals, with its original sum-projection values. -/
def finiteLocalizedNormalFunctional (M : VonNeumannAlgebra H) {I : Type v} :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    (ψ : PositiveContinuousLinearMap ℂ M ℂ) → (p : I → M) →
      (hp : ∀ i, IsStarProjection (p i)) → (ξ : I → H) →
      (∀ i, ∀ b : PositiveElement M,
        @LE.le M (CStarAlgebra.spectralOrder M).toLE (b : M) (p i) →
        (ψ.toContinuousLinearMap (b : M)).re ≤ (vectorFunctional M (ξ i) (ξ i) (b : M)).re) →
      (s : Finset I) → {ρ : normalFunctionalSpace M // ∀ a : M,
        (ρ.val : StrongDual ℂ M) a = ψ.toContinuousLinearMap (a * ∑ i ∈ s, p i)} := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ p hp ξ hlocal s
  let pieces (i : I) := localizedNormalFunctional M ψ (p i) (hp i) (ξ i) (hlocal i)
  let ρ : normalFunctionalSpace M := ∑ i ∈ s, (pieces i).val
  refine ⟨ρ, ?_⟩
  intro a
  have hvalues (i : I) : ((pieces i).val.val : StrongDual ℂ M) a =
      ψ.toContinuousLinearMap (a * p i) := (pieces i).property a
  change ((∑ i ∈ s, (pieces i).val : normalFunctionalSpace M).val : StrongDual ℂ M) a = _
  simp only [Submodule.coe_sum, sum_apply, hvalues, Finset.mul_sum, map_sum]

end

end VonNeumannAlgebra
