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

public import MathlibExt.Analysis.VonNeumannAlgebra.FiniteLocalizedNormalFunctional
public import MathlibExt.Analysis.VonNeumannAlgebra.PositiveFunctionalProjectionResidual
public import MathlibExt.Algebra.Star.StarProjection.FiniteSum

/-!
# Finite normal approximations and projection residual bounds

For a positive bounded functional `ψ`, let `p_i` be pairwise orthogonal star projections with
local vector domination on each interval `0≤b≤p_i`. A finite subset gives `P_s=Σ_i∈s p_i` and
the normal functional `ρ_s(a)=ψ(aP_s)`.

Its continuous-dual norm error satisfies `‖ψ-ρ_s‖≤√(‖ψ‖ |ψ(1-P_s)|)`. The finite sum is a star
projection; no residual estimate or global normality of `ψ` is assumed.
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

/-- **Finite orthogonal localization with a dual norm error bound.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a
positive bounded complex-linear functional for the spectral orders. Let `p_i ∈ M` be star
projections indexed by an arbitrary type `I`, and `ξ_i ∈ H` satisfy `Re ψ(b)≤Re
⟨ξ_i,bξ_i⟩` whenever `0≤b≤p_i`. assume additionally `p_i p_j=0` for `i≠j`. For finite `s`,
the construction returns `ρ_s∈M_*` with `ρ_s(a)=ψ(aP_s)` for `P_s=Σ_i∈s p_i` and
`‖ψ-ρ_s‖≤√(‖ψ‖*|ψ(1-P_s)|)`. -/
def finiteOrthogonalNormalApproximation (M : VonNeumannAlgebra H) {I : Type v} :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    (ψ : PositiveContinuousLinearMap ℂ M ℂ) → (p : I → M) →
      (∀ i, IsStarProjection (p i)) →
      (∀ i j, i ≠ j → p i * p j = 0) → (ξ : I → H) →
      (∀ i, ∀ b : PositiveElement M,
        @LE.le M (CStarAlgebra.spectralOrder M).toLE (b : M) (p i) →
        (ψ.toContinuousLinearMap (b : M)).re ≤ (vectorFunctional M (ξ i) (ξ i) (b : M)).re) →
      (s : Finset I) → {ρ : normalFunctionalSpace M //
        (∀ a : M, (ρ.val : StrongDual ℂ M) a =
          ψ.toContinuousLinearMap (a * ∑ i ∈ s, p i)) ∧
        ‖ψ.toContinuousLinearMap - (ρ.val : StrongDual ℂ M)‖ ≤
          Real.sqrt (‖ψ.toContinuousLinearMap‖ *
            ‖ψ.toContinuousLinearMap (1 - ∑ i ∈ s, p i)‖)} := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ p hp horthogonal ξ hlocal s
  let P : M := ∑ i ∈ s, p i
  have hP : IsStarProjection P :=
    IsStarProjection.finset_sum_of_pairwise_mul_eq_zero s p
      (fun i _hi => hp i) (fun i _hi j _hj hij => horthogonal i j hij)
  let ρ := finiteLocalizedNormalFunctional M ψ p hp ξ hlocal s
  have hvalues : (ρ.val.val : StrongDual ℂ M) =
      ψ.toContinuousLinearMap.comp ((ContinuousLinearMap.mul ℂ M).flip P) := by
    apply ContinuousLinearMap.ext
    intro a
    change (ρ.val.val : StrongDual ℂ M) a = ψ.toContinuousLinearMap (a * P)
    exact ρ.property a
  refine ⟨ρ.val, ρ.property, ?_⟩
  rw [hvalues]
  exact positiveFunctional_rightProjection_residual_norm_le M ψ P hP

end

end VonNeumannAlgebra
