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

public import MathlibExt.MeasureTheory.Function.L2Space.RightTensorProduct
public import MathlibExt.Analysis.InnerProductSpace.TensorProduct.CompletionMap

/-!
# Constant Hilbert operators in tensor L² coordinates

Let X be a measurable space, μ any measure, 𝕜 an RCLike field and H₁,H₂ complete inner product
spaces over 𝕜 in independent universes. For J_i:H_i⊗̂L²(X,μ;𝕜)≃L²(X,μ;H_i),
J_i(x⊗f)(s)=f(s)•x, and a bounded B:H₁→H₂, J₂∘(B⊗̂id)=M_B∘J₁, where M_B acts pointwise by B.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped TensorProduct ENNReal Topology

namespace MeasureTheory.L2

noncomputable section

universe uX uK uH₁ uH₂

variable {X : Type uX} [MeasurableSpace X]
variable {𝕜 : Type uK} [RCLike 𝕜]
variable {H₁ : Type uH₁} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable {H₂ : Type uH₂} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-- **Tensor-to-L² coordinates intertwine a constant operator.**

Let X be measurable, μ any measure, 𝕜 an RCLike field and H₁,H₂ complete inner product spaces.
Let J_i=tensorToLpRight μ:H_i⊗̂L²(X,μ;𝕜)≃L²(X,μ;H_i). For bounded B:H₁→H₂ and z in the first
tensor completion, J₂((B⊗̂id)z)=B.compLpL 2 μ (J₁z), whose representative is s↦B((J₁z)(s))
almost everywhere.
-/
theorem tensorToLpRight_mapLCompletion (μ : Measure X) (B : H₁ →L[𝕜] H₂)
    (z : UniformSpace.Completion (H₁ ⊗[𝕜] (Lp 𝕜 2 μ))) :
    tensorToLpRight μ
        (TensorProduct.mapLCompletion B (ContinuousLinearMap.id 𝕜 (Lp 𝕜 2 μ)) z) =
      B.compLpL 2 μ (tensorToLpRight μ z) := by
  let m : PseudoMetricSpace (UniformSpace.Completion (H₁ ⊗[𝕜] (Lp 𝕜 2 μ))) :=
    (inferInstance : SeminormedAddCommGroup
      (UniformSpace.Completion (H₁ ⊗[𝕜] (Lp 𝕜 2 μ)))).toPseudoMetricSpace
  have hUniform : m.toUniformSpace = UniformSpace.Completion.uniformSpace (H₁ ⊗[𝕜] (Lp 𝕜 2 μ)) := by
    apply UniformSpace.ext
    exact (@PseudoMetricSpace.uniformity_dist _ m).trans
      (UniformSpace.Completion.uniformity_dist (α := H₁ ⊗[𝕜] (Lp 𝕜 2 μ))).symm
  have htop : m.toUniformSpace.toTopologicalSpace =
      (UniformSpace.Completion.uniformSpace (H₁ ⊗[𝕜] (Lp 𝕜 2 μ))).toTopologicalSpace :=
    congrArg (fun w : UniformSpace (UniformSpace.Completion (H₁ ⊗[𝕜] (Lp 𝕜 2 μ))) =>
      @UniformSpace.toTopologicalSpace (UniformSpace.Completion (H₁ ⊗[𝕜] (Lp 𝕜 2 μ))) w) hUniform
  have toStockClosed (s : Set (UniformSpace.Completion (H₁ ⊗[𝕜] (Lp 𝕜 2 μ))))
      (hs : @IsClosed _ m.toUniformSpace.toTopologicalSpace s) :
      @IsClosed _ (UniformSpace.Completion.uniformSpace (H₁ ⊗[𝕜] (Lp 𝕜 2 μ))).toTopologicalSpace s := by
    rw [htop] at hs
    exact hs
  refine UniformSpace.Completion.induction_on z (toStockClosed _
    (isClosed_eq
      ((tensorToLpRight (H := H₂) μ).continuous.comp
        (TensorProduct.mapLCompletion B (ContinuousLinearMap.id 𝕜 (Lp 𝕜 2 μ))).continuous)
      ((B.compLpL 2 μ).continuous.comp (tensorToLpRight (H := H₁) μ).continuous))) ?_
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x f =>
    rw [TensorProduct.mapLCompletion_tmul]
    change tensorToLpRight μ ((B x ⊗ₜ[𝕜] f : H₂ ⊗[𝕜] (Lp 𝕜 2 μ)) :
        UniformSpace.Completion (H₂ ⊗[𝕜] (Lp 𝕜 2 μ))) =
      B.compLpL 2 μ (tensorToLpRight μ ((x ⊗ₜ[𝕜] f : H₁ ⊗[𝕜] (Lp 𝕜 2 μ)) :
        UniformSpace.Completion (H₁ ⊗[𝕜] (Lp 𝕜 2 μ))))
    apply Lp.ext
    filter_upwards [tensorToLpRight_tmul_ae μ (B x) f,
      B.coeFn_compLpL (tensorToLpRight μ ((x ⊗ₜ[𝕜] f : H₁ ⊗[𝕜] (Lp 𝕜 2 μ)) :
        UniformSpace.Completion (H₁ ⊗[𝕜] (Lp 𝕜 2 μ)))),
      tensorToLpRight_tmul_ae μ x f] with s hleft hmap hright
    rw [hleft, hmap, hright, map_smul]
  | add z w hz hw => simp only [UniformSpace.Completion.coe_add, map_add, hz, hw]

end

end MeasureTheory.L2
