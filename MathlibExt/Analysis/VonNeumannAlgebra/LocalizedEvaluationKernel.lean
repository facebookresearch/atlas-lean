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

public import MathlibExt.Analysis.VonNeumannAlgebra.PositiveFunctionalLocalization
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The localized functional factors through its actual operator evaluation

The evaluation map sends a to (a*p)ξ. The original local positive comparison
bounds the squared norm of ψ(a*p) by that vector's squared norm. Consequently
an operator in the evaluation kernel also belongs to the localized
functional's kernel. This is the kernel prerequisite for factorization
through the actual evaluation range; no norm or normality certificate is
supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual bounded operator-evaluation map a ↦ (a*p)ξ retains its continuity. -/
def localizedOperatorEvaluation (M : VonNeumannAlgebra H) (p : M) (ξ : H) : M →L[ℂ] H := by
  let A : M →ₗ[ℂ] H :=
    { toFun := fun a => ((a * p : M) : H →L[ℂ] H) ξ
      map_add' := by
        intro a b
        change (((a : H →L[ℂ] H) + (b : H →L[ℂ] H)) * (p : H →L[ℂ] H)) ξ =
          ((a : H →L[ℂ] H) * (p : H →L[ℂ] H)) ξ +
            ((b : H →L[ℂ] H) * (p : H →L[ℂ] H)) ξ
        rw [add_mul, add_apply]
      map_smul' := by
        intro c a
        simp only [RingHom.id_apply]
        change ((c • (a : H →L[ℂ] H)) * (p : H →L[ℂ] H)) ξ =
          c • (((a : H →L[ℂ] H) * (p : H →L[ℂ] H)) ξ)
        rw [smul_mul_assoc, smul_apply] }
  have hbound (a : M) : ‖A a‖ ≤ (‖p‖ * ‖ξ‖) * ‖a‖ := by
    change ‖((a * p : M) : H →L[ℂ] H) ξ‖ ≤ (‖p‖ * ‖ξ‖) * ‖a‖
    have hmul : ‖((a * p : M) : H →L[ℂ] H)‖ ≤ ‖a‖ * ‖p‖ := norm_mul_le a p
    calc
      ‖((a * p : M) : H →L[ℂ] H) ξ‖ ≤ ‖((a * p : M) : H →L[ℂ] H)‖ * ‖ξ‖ :=
        ((a * p : M) : H →L[ℂ] H).le_opNorm ξ
      _ ≤ (‖a‖ * ‖p‖) * ‖ξ‖ := mul_le_mul_of_nonneg_right hmul (norm_nonneg ξ)
      _ = (‖p‖ * ‖ξ‖) * ‖a‖ := by ring
  exact A.mkContinuous (‖p‖ * ‖ξ‖) hbound

/-- The original right-localized bounded functional retains its continuous linear map. -/
def localizedFunctionalLinearMap (M : VonNeumannAlgebra H) (ψ : StrongDual ℂ M) (p : M) :
    M →L[ℂ] ℂ :=
  ψ.comp ((ContinuousLinearMap.mul ℂ M).flip p)

/-- The original local vector comparison proves the actual evaluation-kernel inclusion. -/
theorem localizedOperatorEvaluation_ker_le (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ) (p : M) (_hp : IsStarProjection p) (ξ : H),
      (∀ b : PositiveElement M,
        @LE.le M (CStarAlgebra.spectralOrder M).toLE (b : M) p →
        (ψ.toContinuousLinearMap (b : M)).re ≤ (vectorFunctional M ξ ξ (b : M)).re) →
      LinearMap.ker (localizedOperatorEvaluation M p ξ).toLinearMap ≤
        LinearMap.ker (localizedFunctionalLinearMap M ψ.toContinuousLinearMap p).toLinearMap := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ p hp ξ hlocal a ha
  have hzero : ((a * p : M) : H →L[ℂ] H) ξ = 0 := ha
  have hbound := localizedPositiveFunctional_norm_sq_le_vector M ψ p hp ξ hlocal a
  rw [hzero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] at hbound
  have hnorm : ‖ψ.toContinuousLinearMap (a * p)‖ = 0 := by
    nlinarith [norm_nonneg (ψ.toContinuousLinearMap (a * p))]
  change ψ.toContinuousLinearMap (a * p) = 0
  exact norm_eq_zero.mp hnorm

end

end VonNeumannAlgebra
