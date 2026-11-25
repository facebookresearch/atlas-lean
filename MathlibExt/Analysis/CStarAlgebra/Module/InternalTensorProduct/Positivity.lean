/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Algebraic
public import MathlibExt.Analysis.CStarAlgebra.Module.Matrix.Gram
import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.MixedGram
import MathlibExt.Analysis.CStarAlgebra.CStarMatrix.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Positivity of the literal balanced tensor inner form

A positive first-factor Gram matrix is amplified by the given nonunital star
homomorphism. The actual square root of that positive operator matrix expands
the printed tensor self-inner as a sum of second-factor self-inners.

The conclusion uses the SAME caller opposite-coefficient order. No order
transport, positive model, tensor norm, null quotient or completion is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped TensorProduct BigOperators RightActions

namespace CStarModule.InternalTensorProduct

universe uB₁ uB₂ uE₁ uE₂ uI

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁] [PartialOrder B₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂] [PartialOrder B₂ᵐᵒᵖ]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
variable [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
variable [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂]

section Hilbert

variable [StarOrderedRing B₁ᵐᵒᵖ] [CompleteSpace E₁]
variable [StarOrderedRing B₂ᵐᵒᵖ] [CompleteSpace E₂]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. For a finite family of elementary tensors, the self-inner product of their sum is
nonnegative in the positive order of the opposite coefficient algebra B₂ᵐᵒᵖ. -/
theorem rawInner_sum_self_nonneg {I : Type uI} [Fintype I]
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x : I → E₁) (u : I → E₂) :
    0 ≤ MulOpposite.op
      (rawInner φ (∑ i, x i ⊗ₜ[ℂ] u i) (∑ i, x i ⊗ₜ[ℂ] u i)) := by
  let : PartialOrder B₁ := CStarAlgebra.spectralOrder B₁
  let : StarOrderedRing B₁ := CStarAlgebra.spectralOrderedRing B₁
  let : PartialOrder (AdjointableOperator.End B₂ E₂) :=
    CStarAlgebra.spectralOrder (AdjointableOperator.End B₂ E₂)
  let : StarOrderedRing (AdjointableOperator.End B₂ E₂) :=
    CStarAlgebra.spectralOrderedRing (AdjointableOperator.End B₂ E₂)
  let G : CStarMatrix I I B₁ :=
    CStarMatrix.ofMatrix fun i j => rightInner (B := B₁) (x i) (x j)
  let M : CStarMatrix I I (AdjointableOperator.End B₂ E₂) :=
    CStarMatrix.mapₙₐ φ G
  let : PartialOrder (CStarMatrix I I B₁) :=
    CStarAlgebra.spectralOrder (CStarMatrix I I B₁)
  let : StarOrderedRing (CStarMatrix I I B₁) :=
    CStarAlgebra.spectralOrderedRing (CStarMatrix I I B₁)
  let : PartialOrder (CStarMatrix I I (AdjointableOperator.End B₂ E₂)) :=
    CStarAlgebra.spectralOrder _
  let : StarOrderedRing (CStarMatrix I I (AdjointableOperator.End B₂ E₂)) :=
    CStarAlgebra.spectralOrderedRing _
  have hG : (0 : CStarMatrix I I B₁) ≤ G :=
    AdjointableOperator.gramMatrix_nonneg x
  have hM : (0 : CStarMatrix I I (AdjointableOperator.End B₂ E₂)) ≤ M :=
    map_nonneg (CStarMatrix.mapₙₐ φ) hG
  let : NonUnitalContinuousFunctionalCalculus ℝ
      (CStarMatrix I I (AdjointableOperator.End B₂ E₂)) IsSelfAdjoint :=
    (IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
      (A := CStarMatrix I I
          (AdjointableOperator.End B₂ E₂))).toNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ
      (CStarMatrix I I (AdjointableOperator.End B₂ E₂)) :=
    CStarAlgebra.instNonnegSpectrumClass'
      (A := CStarMatrix I I (AdjointableOperator.End B₂ E₂))
  let R : CStarMatrix I I (AdjointableOperator.End B₂ E₂) := CFC.sqrt M
  have hRstar : star R = R :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg M)).star_eq
  have hRR : star R * R = M := by
    rw [hRstar]
    exact CFC.sqrt_mul_sqrt_self M hM
  have hMap : M =
      CStarMatrix.ofMatrix fun i j => φ (rightInner (B := B₁) (x i) (x j)) := by
    rfl
  have hInner :
      rawInner φ (∑ i, x i ⊗ₜ[ℂ] u i) (∑ i, x i ⊗ₜ[ℂ] u i) =
        ∑ k, rightInner (B := B₂)
          (∑ i, R k i (u i)) (∑ i, R k i (u i)) := by
    rw [rawInner_sum_tmul_sum_tmul]
    calc
      _ = ∑ i, ∑ j, rightInner (B := B₂) (u i) (M i j (u j)) := by
        rw [hMap]
        rfl
      _ = ∑ i, ∑ j,
          rightInner (B := B₂) (u i) ((star R * R) i j (u j)) := by
        rw [hRR]
      _ = ∑ k, rightInner (B := B₂)
          (∑ i, R k i (u i)) (∑ i, R k i (u i)) :=
        matrix_star_mul_mixed_inner R u u
  have hOp :
      MulOpposite.op
          (rawInner φ (∑ i, x i ⊗ₜ[ℂ] u i) (∑ i, x i ⊗ₜ[ℂ] u i)) =
        ∑ k, inner B₂ᵐᵒᵖ (∑ i, R k i (u i)) (∑ i, R k i (u i)) := by
    rw [hInner]
    calc
      _ = ∑ k, MulOpposite.op
          (rightInner (B := B₂) (∑ i, R k i (u i)) (∑ i, R k i (u i))) :=
        map_sum MulOpposite.opAddEquiv _ _
      _ = ∑ k, inner B₂ᵐᵒᵖ (∑ i, R k i (u i)) (∑ i, R k i (u i)) := by
        rfl
  rw [hOp]
  exact Finset.sum_nonneg fun k hk =>
    CStarModule.inner_self_nonneg
      (A := B₂ᵐᵒᵖ) (E := E₂) (x := ∑ i, R k i (u i))

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Every algebraic tensor has nonnegative self-inner product in the positive order of B₂ᵐᵒᵖ. -/
theorem rawInner_self_nonneg
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (z : AlgebraicTensor E₁ E₂) :
    0 ≤ MulOpposite.op (rawInner φ z z) := by
  classical
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset z
  have hsum : z = ∑ p : s, p.1.1 ⊗ₜ[ℂ] p.1.2 := by
    calc
      z = ∑ p ∈ s, p.1 ⊗ₜ[ℂ] p.2 := hs
      _ = ∑ p : s, p.1.1 ⊗ₜ[ℂ] p.1.2 :=
        (Finset.sum_coe_sort s
          (fun p : E₁ × E₂ => p.1 ⊗ₜ[ℂ] p.2)).symm
  rw [hsum]
  exact rawInner_sum_self_nonneg φ (fun p : s => p.1.1) (fun p : s => p.1.2)

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Every balanced tensor has nonnegative self-inner product in the positive order of B₂ᵐᵒᵖ. -/
theorem balancedInner_self_nonneg
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (z : BalancedTensor (E₁ := E₁) φ) :
    0 ≤ MulOpposite.op (balancedInner φ z z) := by
  obtain ⟨w, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective z
  simpa only [balancedInner_mkQ_mkQ] using rawInner_self_nonneg φ w

end Hilbert

end CStarModule.InternalTensorProduct
