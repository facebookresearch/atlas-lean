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

public import MathlibExt.Analysis.VonNeumannAlgebra.Ultraweak
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The actual predual pullback of fixed star conjugation

The stock bounded left/right multiplication map sends a to star x * a * x.
Its functional pullback sends each original vector coefficient to the
coefficient with both vectors multiplied by the same x. The actual closed
normal-functional span is therefore invariant. Restricting the stock
functional pullback constructs the continuous linear map on that predual.

This proves ultraweak continuity of the same literal conjugation map.
It supplies the normal-conjugation prerequisite for the original bounded
positive LUB/weight-normality construction. It does not identify positive
LUBs with ultraweak limits or supply a normal weight/GNS representation.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Fixed literal star conjugation has its actual bounded pullback on the original normal predual. -/
def normalFunctionalConjugationPullback (M : VonNeumannAlgebra H) (x : M) :
    normalFunctionalSpace M →L[ℂ] normalFunctionalSpace M := by
  let C : M →L[ℂ] M := ContinuousLinearMap.mulLeftRight ℂ M (star x) x
  let B : StrongDual ℂ M →L[ℂ] StrongDual ℂ M := (ContinuousLinearMap.compL ℂ M M ℂ).flip C
  let P : Submodule ℂ (StrongDual ℂ M) := (normalFunctionalSpace M).comap B.toLinearMap
  have hP : IsClosed (P : Set (StrongDual ℂ M)) := by
    change IsClosed (B ⁻¹' (normalFunctionalSpace M : Set (StrongDual ℂ M)))
    exact (normalFunctionalSpace_isClosed M).preimage B.continuous
  have hvec : ∀ ξ η : H, vectorFunctional M ξ η ∈ P := by
    intro ξ η
    change B (vectorFunctional M ξ η) ∈ normalFunctionalSpace M
    have hshift : B (vectorFunctional M ξ η) =
        vectorFunctional M ((x : H →L[ℂ] H) ξ) ((x : H →L[ℂ] H) η) := by
      apply ContinuousLinearMap.ext
      intro a
      change vectorFunctional M ξ η (star x * a * x) =
        vectorFunctional M ((x : H →L[ℂ] H) ξ) ((x : H →L[ℂ] H) η) a
      rw [vectorFunctional_apply, vectorFunctional_apply]
      change ⟪ξ, (star (x : H →L[ℂ] H) * (a : H →L[ℂ] H) * (x : H →L[ℂ] H)) η⟫_ℂ =
        ⟪(x : H →L[ℂ] H) ξ, (a : H →L[ℂ] H) ((x : H →L[ℂ] H) η)⟫_ℂ
      rw [mul_apply_eq_comp, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right]
    rw [hshift]
    exact vectorFunctional_mem_normalFunctionalSpace M
      ((x : H →L[ℂ] H) ξ) ((x : H →L[ℂ] H) η)
  have hle : normalFunctionalSpace M ≤ P := normalFunctionalSpace_le M hP hvec
  let T := B.comp (normalFunctionalSpace M).subtypeL
  exact T.codRestrict (normalFunctionalSpace M) fun ψ => hle ψ.property

/-- The constructed predual map has exactly the original star-conjugation functional values. -/
theorem normalFunctionalConjugationPullback_apply (M : VonNeumannAlgebra H) (x : M)
    (ψ : normalFunctionalSpace M) (a : M) :
    (normalFunctionalConjugationPullback M x ψ : StrongDual ℂ M) a =
      (ψ : StrongDual ℂ M) (star x * a * x) :=
  rfl

/-- The same literal fixed star conjugation is continuous for the actual ultraweak topology. -/
theorem ultraweak_starConjugation_continuous (M : VonNeumannAlgebra H) (x : M) :
    Continuous (fun a : Ultraweak M =>
      (ultraweakLinearEquiv M).symm (star x * ultraweakLinearEquiv M a * x)) := by
  apply (ultraweak_continuous_iff M).2
  intro ψ
  let ψx : normalFunctionalSpace M := normalFunctionalConjugationPullback M x ψ
  have hcontinuous := ultraweak_eval_continuous M ψx
  change Continuous (fun a : Ultraweak M =>
    (normalFunctionalConjugationPullback M x ψ : StrongDual ℂ M) (ultraweakLinearEquiv M a)) at hcontinuous
  change Continuous (fun a : Ultraweak M =>
    (ψ : StrongDual ℂ M) (star x * ultraweakLinearEquiv M a * x))
  simpa only [normalFunctionalConjugationPullback_apply] using hcontinuous

end

end VonNeumannAlgebra
