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
# Fixed multiplication and normal-functional pullback

For a concrete von Neumann algebra `M` and fixed `a ∈ M`, left multiplication `x ↦ ax` gives the
bounded functional pullback `ψ ↦ (x ↦ ψ(ax))` on `M*`.

It sends a vector functional `ω_(ξ,η)` to `ω_(a*ξ,η)` and preserves the normal-functional
subspace `M_*`. Consequently fixed left multiplication is ultraweakly continuous. Joint
ultraweak continuity of multiplication is not asserted.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

noncomputable section

namespace VonNeumannAlgebra

universe uH

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Bounded dual pullback of fixed left multiplication.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. for `a ∈ M`,
`normalFunctionalLeftPullback M a : M* →L[ℂ] M*` sends `ψ` to `x ↦ ψ(ax)`. -/
def normalFunctionalLeftPullback (M : VonNeumannAlgebra H) (a : M) :
    StrongDual ℂ M →L[ℂ] StrongDual ℂ M :=
  (ContinuousLinearMap.compL ℂ M M ℂ).flip (ContinuousLinearMap.mul ℂ M a)

/-- **Value of fixed-left functional pullback.** Let `H` be a complete complex Hilbert space
and `M ⊆ B(H)` a concrete von Neumann algebra. for `a,x ∈ M` and `ψ ∈ M*`,
`normalFunctionalLeftPullback M a ψ x=ψ(a*x)`. -/
theorem normalFunctionalLeftPullback_apply (M : VonNeumannAlgebra H) (a : M)
    (ψ : StrongDual ℂ M) (x : M) : normalFunctionalLeftPullback M a ψ x = ψ (a * x) :=
  rfl

/-- **Adjoint shift of a vector coefficient under left multiplication.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. for `a ∈ M` and `ξ,η ∈ H`,
`normalFunctionalLeftPullback M a (ω_(ξ,η))=ω_(a*ξ,η)`. -/
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

/-- **Normal-functional space invariant under left-multiplication pullback.** Let `H` be a
complete complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. for `a ∈ M` and `ψ ∈ M_*`, `normalFunctionalLeftPullback
M a ψ∈M_*`. -/
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

/-- **Ultraweak continuity of fixed left multiplication.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. for every fixed `a ∈ M`, `x ↦ a*x` is continuous on `M` with its ultraweak topology. -/
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
