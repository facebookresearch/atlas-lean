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

public import MathlibExt.Analysis.InnerProductSpace.TensorProduct.InsideCompletion
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Product Hilbert bases in the tensor completion

Given Hilbert bases of two inner-product spaces, their completed pure
tensors form a Hilbert basis of the actual tensor completion. Its lp-two
representation sends a pure tensor to the products of the original basis
coordinates. Scalar, factor and index universes are independent, and the index types
need not be finite, countable, or nonempty. The given Hilbert bases entail completeness
of their factor spaces; the construction requires no additional completeness argument.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open UniformSpace
open scoped TensorProduct

namespace HilbertBasis

universe u𝕜 uE uF uI uJ
variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable {ι : Type uI} {κ : Type uJ}

/-- Let `𝕜` be a real or complex scalar field (`RCLike 𝕜`), and let `E` and `F` be
independent normed inner-product spaces over `𝕜`. Let `b : HilbertBasis ι 𝕜 E` and
`c : HilbertBasis κ 𝕜 F` be Hilbert bases with arbitrary independent index types.
The family `(i,j) ↦ b i ⊗ c j`, included in the actual Hilbert tensor completion,
is a Hilbert basis of `Completion (E ⊗[𝕜] F)` with its tensor inner-product norm.
Zero factors and empty index types are included. -/
def completedTensorProduct (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) :
    HilbertBasis (ι × κ) 𝕜 (Completion (E ⊗[𝕜] F)) := by
  let v : ι × κ → Completion (E ⊗[𝕜] F) :=
    fun ij => ((b ij.1 ⊗ₜ[𝕜] c ij.2 : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F))
  have hv : Orthonormal 𝕜 v := by
    exact (b.orthonormal.tmul c.orthonormal).comp_linearIsometry
      (Completion.toComplₗᵢ (𝕜 := 𝕜) (E := E ⊗[𝕜] F))
  have hb : Dense (Submodule.span 𝕜 (Set.range b) : Set E) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span
  have hc : Dense (Submodule.span 𝕜 (Set.range c) : Set F) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr c.dense_span
  have hset :
      {z : Completion (E ⊗[𝕜] F) | ∃ x ∈ Set.range b, ∃ y ∈ Set.range c,
        z = (x ⊗ₜ[𝕜] y : Completion (E ⊗[𝕜] F))} = Set.range v := by
    ext z
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, y, ⟨j, rfl⟩, rfl⟩
      exact ⟨(i, j), rfl⟩
    · rintro ⟨⟨i, j⟩, rfl⟩
      exact ⟨b i, ⟨i, rfl⟩, c j, ⟨j, rfl⟩, rfl⟩
  have hdense := TensorProduct.dense_span_completed_tmul (Set.range b) (Set.range c) hb hc
  rw [hset] at hdense
  exact HilbertBasis.mk hv
    (Submodule.dense_iff_topologicalClosure_eq_top.mp hdense).ge

/-- Let `𝕜` be a real or complex scalar field (`RCLike 𝕜`), and let `E` and `F` be
independent normed inner-product spaces over `𝕜`. Let `b : HilbertBasis ι 𝕜 E` and
`c : HilbertBasis κ 𝕜 F` be Hilbert bases with arbitrary independent index types.
For every `i : ι` and `j : κ`, the product basis vector at `(i,j)` is exactly
the completed pure tensor of `b i` and `c j` in `Completion (E ⊗[𝕜] F)`,
with its actual tensor inner-product norm. -/
@[simp]
theorem completedTensorProduct_apply (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (i : ι) (j : κ) :
    completedTensorProduct b c (i, j) =
      ((b i ⊗ₜ[𝕜] c j : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) := by
  unfold completedTensorProduct
  exact congrFun (HilbertBasis.coe_mk _ _) (i, j)

/-- Let `𝕜` be a real or complex scalar field (`RCLike 𝕜`), and let `E` and `F` be
independent normed inner-product spaces over `𝕜`. Let `b : HilbertBasis ι 𝕜 E` and
`c : HilbertBasis κ 𝕜 F` be Hilbert bases with arbitrary independent index types.
For every `x : E`, `y : F`, `i : ι` and `j : κ`, coordinate `(i,j)` of the
completed pure tensor `x ⊗ y` under the product-basis lp-two representation is
`b.repr x i * c.repr y j`. The tensor completion has its actual inner-product norm. -/
theorem completedTensorProduct_repr_tmul (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (x : E) (y : F) (i : ι) (j : κ) :
    (completedTensorProduct b c).repr (x ⊗ₜ[𝕜] y : Completion (E ⊗[𝕜] F)) (i, j) =
      b.repr x i * c.repr y j := by
  rw [HilbertBasis.repr_apply_apply, completedTensorProduct_apply,
    Completion.inner_coe, TensorProduct.inner_tmul]
  have hi := b.repr_apply_apply x i
  have hj := c.repr_apply_apply y j
  rw [← hi, ← hj]

end HilbertBasis
