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
# Kernel factorization of a projection-localized functional

For `p∈M` and `ξ∈H`, evaluation is the bounded map `E_(p,ξ)(a)=(ap)ξ`. For a bounded functional
`ψ`, its right localization is `L_(ψ,p)(a)=ψ(ap)`.

If `ψ` is positive, `p` a star projection and the vector coefficient of `ξ` dominates `Re ψ` on
`0≤b≤p`, then `ker E_(p,ξ) ⊆ ker L_(ψ,p)`. The two map definitions themselves do not require
positivity or the projection condition.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Bounded evaluation after right multiplication.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. for any `p∈M`, `ξ∈H`,
`localizedOperatorEvaluation M p ξ : M →L[ℂ] H` sends `a` to `(ap)ξ`; `p` need not be a
projection. -/
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

/-- **Bounded right-localized functional.** Let `H` be a complete complex Hilbert space and `M
⊆ B(H)` a concrete von Neumann algebra. for any `ψ∈M*` and `p∈M`,
`localizedFunctionalLinearMap M ψ p : M →L[ℂ] ℂ` is `a ↦ ψ(ap)`, without positivity
assumptions. -/
def localizedFunctionalLinearMap (M : VonNeumannAlgebra H) (ψ : StrongDual ℂ M) (p : M) :
    M →L[ℂ] ℂ :=
  ψ.comp ((ContinuousLinearMap.mul ℂ M).flip p)

/-- **Local vector domination gives an evaluation-kernel inclusion.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a
positive bounded complex-linear functional for the spectral orders. Let `p ∈ M` be a star
projection and `ξ ∈ H` satisfy `Re ψ(b)≤Re ⟨ξ,bξ⟩` for every positive `b≤p`. if `(ap)ξ=0`,
then `ψ(ap)=0` for `a∈M`; equivalently the kernel of `a ↦ (ap)ξ` is contained in the
kernel of `a ↦ ψ(ap)`. -/
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
