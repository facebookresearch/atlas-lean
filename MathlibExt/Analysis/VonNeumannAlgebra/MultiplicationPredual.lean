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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalFunctional
public import MathlibExt.Analysis.VonNeumannAlgebra.Ultraweak
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Fixed multiplication on the actual normal predual and ultraweak algebra

Original fixed-left multiplication pulls the actual bounded functional
back by its literal product formula. Vector coefficients become the
original adjoint-shifted vector coefficients. This preserves the actual
norm-closed normal-functional span and proves continuity in the original
ultraweak view. No scalar weight or GNS supplier is needed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

noncomputable section

namespace VonNeumannAlgebra

universe uH

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual bounded functional precomposition by original fixed-left multiplication. -/
def normalFunctionalLeftPullback (M : VonNeumannAlgebra H) (a : M) :
    StrongDual ℂ M →L[ℂ] StrongDual ℂ M :=
  (ContinuousLinearMap.compL ℂ M M ℂ).flip (ContinuousLinearMap.mul ℂ M a)

/-- The original bounded functional pullback has the literal original product value. -/
theorem normalFunctionalLeftPullback_apply (M : VonNeumannAlgebra H) (a : M)
    (ψ : StrongDual ℂ M) (x : M) : normalFunctionalLeftPullback M a ψ x = ψ (a * x) :=
  rfl

/-- Fixed-left pullback of an original vector coefficient is the original adjoint-shifted coefficient. -/
theorem normalFunctionalLeftPullback_vectorFunctional (M : VonNeumannAlgebra H) (a : M)
    (ξ η : H) :
    normalFunctionalLeftPullback M a (vectorFunctional M ξ η) =
      vectorFunctional M (((star a : M) : H →L[ℂ] H) ξ) η := by
  apply ContinuousLinearMap.ext
  intro x
  rw [normalFunctionalLeftPullback_apply, vectorFunctional_apply, vectorFunctional_apply]
  change ⟪ξ, (a : H →L[ℂ] H) ((x : H →L[ℂ] H) η)⟫_ℂ =
    ⟪(ContinuousLinearMap.adjoint (a : H →L[ℂ] H)) ξ, (x : H →L[ℂ] H) η⟫_ℂ
  exact (ContinuousLinearMap.adjoint_inner_left (a : H →L[ℂ] H)
    ((x : H →L[ℂ] H) η) ξ).symm

/-- The actual norm-closed normal-functional span is invariant under original fixed-left pullback. -/
theorem normalFunctionalLeftPullback_mem (M : VonNeumannAlgebra H) (a : M)
    (ψ : StrongDual ℂ M) (hψ : ψ ∈ normalFunctionalSpace M) :
    normalFunctionalLeftPullback M a ψ ∈ normalFunctionalSpace M := by
  let P : Submodule ℂ (StrongDual ℂ M) :=
    (normalFunctionalSpace M).comap (normalFunctionalLeftPullback M a).toLinearMap
  have hP : IsClosed (P : Set (StrongDual ℂ M)) := by
    change IsClosed ((normalFunctionalLeftPullback M a) ⁻¹'
      (normalFunctionalSpace M : Set (StrongDual ℂ M)))
    exact (normalFunctionalSpace_isClosed M).preimage (normalFunctionalLeftPullback M a).continuous
  have hvec : ∀ ξ η : H, vectorFunctional M ξ η ∈ P := by
    intro ξ η
    change normalFunctionalLeftPullback M a (vectorFunctional M ξ η) ∈ normalFunctionalSpace M
    rw [normalFunctionalLeftPullback_vectorFunctional]
    exact vectorFunctional_mem_normalFunctionalSpace M (((star a : M) : H →L[ℂ] H) ξ) η
  have hle : normalFunctionalSpace M ≤ P := normalFunctionalSpace_le M hP hvec
  exact hle hψ

/-- Original fixed-left multiplication is continuous for the actual ultraweak topology. -/
theorem ultraweak_left_mul_continuous (M : VonNeumannAlgebra H) (a : M) :
    Continuous (fun x : Ultraweak M => (ultraweakLinearEquiv M).symm (a * ultraweakLinearEquiv M x)) := by
  apply (ultraweak_continuous_iff M).2
  intro ψ
  let ψa : normalFunctionalSpace M :=
    ⟨normalFunctionalLeftPullback M a (ψ : StrongDual ℂ M),
      normalFunctionalLeftPullback_mem M a (ψ : StrongDual ℂ M) ψ.property⟩
  have hcontinuous := ultraweak_eval_continuous M ψa
  change Continuous (fun x : Ultraweak M =>
    normalFunctionalLeftPullback M a (ψ : StrongDual ℂ M) (ultraweakLinearEquiv M x)) at hcontinuous
  change Continuous (fun x : Ultraweak M => (ψ : StrongDual ℂ M) (a * ultraweakLinearEquiv M x))
  simpa only [normalFunctionalLeftPullback_apply] using hcontinuous


end VonNeumannAlgebra

end
