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

public import MathlibExt.Analysis.InnerProductSpace.TensorProduct.CyclicCompletion
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Moving an actual completion inside the original Hilbert tensor

The original completion inclusion tensors with identity. Its completed stock
isometry has dense range by actual dense coefficient spans, hence is onto.
These are the inside-completion constructor fields needed for the original
mixed-factor Radon L2 carrier. Zero factors and independent universes remain.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set UniformSpace
open scoped TensorProduct

namespace TensorProduct

noncomputable section

universe u𝕜 uE uF

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The actual stock inclusion of a factor into its original uniform completion. -/
def factorCompletionInclusion : E →ₗᵢ[𝕜] Completion E := by
  let _ : UniformContinuousConstSMul 𝕜 E :=
    uniformContinuousConstSMul_of_continuousConstSMul 𝕜 E
  exact Completion.toComplₗᵢ

/-- Tensor the original left completion inclusion with identity, then complete that actual map. -/
def completionLeftTensorEmbedding :
    Completion (E ⊗[𝕜] F) →ₗᵢ[𝕜] Completion ((Completion E) ⊗[𝕜] F) :=
  (mapIsometry (factorCompletionInclusion (𝕜 := 𝕜) (E := E)) (LinearIsometry.id : F →ₗᵢ[𝕜] F)).completion

/-- The actual left inside-completion map retains the literal original completed pure tensor. -/
theorem completionLeftTensorEmbedding_tmul (x : E) (y : F) :
    completionLeftTensorEmbedding (𝕜 := 𝕜)
        ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) =
      (((x : Completion E) ⊗ₜ[𝕜] y : (Completion E) ⊗[𝕜] F) :
        Completion ((Completion E) ⊗[𝕜] F)) := by
  rw [completionLeftTensorEmbedding, LinearIsometry.completion_apply_coe]
  simp only [mapIsometry_apply, TensorProduct.map_tmul, LinearIsometry.id_apply]
  rfl

/-- The actual completed left inclusion has dense range in the original target completion. -/
theorem denseRange_completionLeftTensorEmbedding :
    DenseRange (completionLeftTensorEmbedding (𝕜 := 𝕜) (E := E) (F := F)) := by
  let s : Set (Completion E) := range ((↑) : E → Completion E)
  let t : Set F := univ
  have hs : Dense (Submodule.span 𝕜 s : Set (Completion E)) := by
    intro x
    exact (closure_mono Submodule.subset_span) (Completion.denseRange_coe x)
  have ht : Dense (Submodule.span 𝕜 t : Set F) := by
    simpa only [t, Submodule.span_univ, Submodule.top_coe] using (dense_univ : Dense (univ : Set F))
  let P : Set (Completion ((Completion E) ⊗[𝕜] F)) :=
    {z | ∃ x ∈ s, ∃ y ∈ t,
      z = (x ⊗ₜ[𝕜] y : Completion ((Completion E) ⊗[𝕜] F))}
  have hP : Dense (Submodule.span 𝕜 P : Set (Completion ((Completion E) ⊗[𝕜] F))) :=
    dense_span_completed_tmul s t hs ht
  have hSpan : Submodule.span 𝕜 P ≤
      (completionLeftTensorEmbedding (𝕜 := 𝕜) (E := E) (F := F)).toLinearMap.range := by
    apply Submodule.span_le.mpr
    rintro z ⟨x, ⟨a, rfl⟩, y, _hy, rfl⟩
    exact ⟨((a ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)),
      completionLeftTensorEmbedding_tmul a y⟩
  intro z
  exact (closure_mono hSpan) (hP z)

/-- Actual density and complete-source isometry prove the left inside-completion map is onto. -/
theorem surjective_completionLeftTensorEmbedding :
    Function.Surjective (completionLeftTensorEmbedding (𝕜 := 𝕜) (E := E) (F := F)) := by
  let I := completionLeftTensorEmbedding (𝕜 := 𝕜) (E := E) (F := F)
  have hclosed : IsClosed (range I) := I.isometry.isClosedEmbedding.isClosed_range
  intro z
  have hz : z ∈ closure (range I) := denseRange_completionLeftTensorEmbedding z
  rw [hclosed.closure_eq] at hz
  exact hz

/-- The original stock tensor completion equals the tensor with its left factor completed inside. -/
def completionLeftTensorUnitary :
    Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] Completion ((Completion E) ⊗[𝕜] F) :=
  LinearIsometryEquiv.ofSurjective (completionLeftTensorEmbedding (𝕜 := 𝕜))
    (surjective_completionLeftTensorEmbedding (𝕜 := 𝕜))

/-- Tensor identity with the original right completion inclusion, then complete the actual map. -/
def completionRightTensorEmbedding :
    Completion (E ⊗[𝕜] F) →ₗᵢ[𝕜] Completion (E ⊗[𝕜] (Completion F)) :=
  (mapIsometry (LinearIsometry.id : E →ₗᵢ[𝕜] E) (factorCompletionInclusion (𝕜 := 𝕜) (E := F))).completion

/-- The actual right inside-completion map retains the literal original completed pure tensor. -/
theorem completionRightTensorEmbedding_tmul (x : E) (y : F) :
    completionRightTensorEmbedding (𝕜 := 𝕜)
        ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) =
      ((x ⊗ₜ[𝕜] (y : Completion F) : E ⊗[𝕜] (Completion F)) :
        Completion (E ⊗[𝕜] (Completion F))) := by
  rw [completionRightTensorEmbedding, LinearIsometry.completion_apply_coe]
  simp only [mapIsometry_apply, TensorProduct.map_tmul, LinearIsometry.id_apply]
  rfl

/-- Actual dense right coefficient spans give dense range of the original completed right map. -/
theorem denseRange_completionRightTensorEmbedding :
    DenseRange (completionRightTensorEmbedding (𝕜 := 𝕜) (E := E) (F := F)) := by
  let s : Set E := univ
  let t : Set (Completion F) := range ((↑) : F → Completion F)
  have hs : Dense (Submodule.span 𝕜 s : Set E) := by
    simpa only [s, Submodule.span_univ, Submodule.top_coe] using (dense_univ : Dense (univ : Set E))
  have ht : Dense (Submodule.span 𝕜 t : Set (Completion F)) := by
    intro y
    exact (closure_mono Submodule.subset_span) (Completion.denseRange_coe y)
  let P : Set (Completion (E ⊗[𝕜] (Completion F))) :=
    {z | ∃ x ∈ s, ∃ y ∈ t,
      z = (x ⊗ₜ[𝕜] y : Completion (E ⊗[𝕜] (Completion F)))}
  have hP : Dense (Submodule.span 𝕜 P : Set (Completion (E ⊗[𝕜] (Completion F)))) :=
    dense_span_completed_tmul s t hs ht
  have hSpan : Submodule.span 𝕜 P ≤
      (completionRightTensorEmbedding (𝕜 := 𝕜) (E := E) (F := F)).toLinearMap.range := by
    apply Submodule.span_le.mpr
    rintro z ⟨x, _hx, y, ⟨b, rfl⟩, rfl⟩
    exact ⟨((x ⊗ₜ[𝕜] b : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)),
      completionRightTensorEmbedding_tmul x b⟩
  intro z
  exact (closure_mono hSpan) (hP z)

/-- The actual completed right inclusion is onto by complete-source isometry and proved density. -/
theorem surjective_completionRightTensorEmbedding :
    Function.Surjective (completionRightTensorEmbedding (𝕜 := 𝕜) (E := E) (F := F)) := by
  let I := completionRightTensorEmbedding (𝕜 := 𝕜) (E := E) (F := F)
  have hclosed : IsClosed (range I) := I.isometry.isClosedEmbedding.isClosed_range
  intro z
  have hz : z ∈ closure (range I) := denseRange_completionRightTensorEmbedding z
  rw [hclosed.closure_eq] at hz
  exact hz

/-- The original stock tensor completion equals the tensor with its right factor completed inside. -/
def completionRightTensorUnitary :
    Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] Completion (E ⊗[𝕜] (Completion F)) :=
  LinearIsometryEquiv.ofSurjective (completionRightTensorEmbedding (𝕜 := 𝕜))
    (surjective_completionRightTensorEmbedding (𝕜 := 𝕜))

end

end TensorProduct
