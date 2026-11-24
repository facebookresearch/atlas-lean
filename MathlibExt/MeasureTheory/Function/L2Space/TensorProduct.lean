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

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# The completed scalar L2 tensor is the actual Hilbert-valued L2 space

The carrier is the stock completion of the stock inner-product tensor norm.
Its comparison sends a pure tensor to pointwise scalar multiplication. The
inner-product integral proves isometry; finite-measure indicators and the
existing Lp induction theorem prove surjectivity for an arbitrary measure.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped TensorProduct ENNReal InnerProductSpace

namespace MeasureTheory.L2

noncomputable section

universe uX uH uK

variable {X : Type uX} [MeasurableSpace X]
variable {𝕜 : Type uK} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable (μ : Measure X)

/-- Pointwise scalar multiplication, computed by the existing Lp composition functor. -/
def scalarVector : Lp 𝕜 2 μ →L[𝕜] H →L[𝕜] Lp H 2 μ :=
  ((ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] H →L[𝕜] H).flip.compLpL₂ 2 μ).flip

/-- The actual scalar-vector Lp map has its original pointwise representative almost everywhere. -/
theorem scalarVector_ae_eq (f : Lp 𝕜 2 μ) (x : H) :
    scalarVector μ f x =ᵐ[μ] fun s => f s • x := by
  change (ContinuousLinearMap.toSpanSingleton 𝕜 x).compLp f =ᵐ[μ] fun s => f s • x
  exact (ContinuousLinearMap.toSpanSingleton 𝕜 x).coeFn_compLp f

/-- The actual pointwise integral has the stock pure-tensor inner product. -/
private theorem scalarVector_inner (f g : Lp 𝕜 2 μ) (x y : H) :
    inner 𝕜 (scalarVector μ f x) (scalarVector μ g y) = inner 𝕜 f g * inner 𝕜 x y := by
  change inner 𝕜 ((ContinuousLinearMap.toSpanSingleton 𝕜 x).compLp f)
      ((ContinuousLinearMap.toSpanSingleton 𝕜 y).compLp g) = inner 𝕜 f g * inner 𝕜 x y
  simp only [L2.inner_def]
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [(ContinuousLinearMap.toSpanSingleton 𝕜 x).coeFn_compLp f,
    (ContinuousLinearMap.toSpanSingleton 𝕜 y).coeFn_compLp g] with s hx hy
  rw [hx, hy, ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.toSpanSingleton_apply]
  simp only [inner_smul_left, inner_smul_right, RCLike.inner_apply', mul_assoc]
  exact mul_left_comm _ _ _

/-- The algebraic tensor lift of the computed pointwise bilinear map. -/
def tensorToLpLinearMap : (Lp 𝕜 2 μ) ⊗[𝕜] H →ₗ[𝕜] Lp H 2 μ :=
  TensorProduct.lift (scalarVector μ).toLinearMap₁₂

/-- The actual algebraic lift sends each pure tensor to its original scalar-vector Lp value. -/
@[simp]
theorem tensorToLpLinearMap_tmul (f : Lp 𝕜 2 μ) (x : H) :
    tensorToLpLinearMap μ (f ⊗ₜ[𝕜] x) = (ContinuousLinearMap.toSpanSingleton 𝕜 x).compLp f := by
  change TensorProduct.lift (scalarVector μ).toLinearMap₁₂ (f ⊗ₜ[𝕜] x) = _
  rw [TensorProduct.lift.tmul]
  rfl

/-- The lift preserves the actual tensor inner product, by bilinearity on pure tensors. -/
theorem tensorToLpLinearMap_inner (z w : (Lp 𝕜 2 μ) ⊗[𝕜] H) :
    inner 𝕜 (tensorToLpLinearMap μ z) (tensorToLpLinearMap μ w) = inner 𝕜 z w := by
  induction z using TensorProduct.inductionOn with
  | tmul f x =>
    induction w using TensorProduct.inductionOn with
    | tmul g y =>
      change inner 𝕜 (scalarVector μ f x) (scalarVector μ g y) = inner 𝕜 f g * inner 𝕜 x y
      exact scalarVector_inner μ f g x y
    | add z w hz hw => simp only [map_add, inner_add_right, hz, hw]
  | add z w hz hw => simp only [map_add, inner_add_left, hz, hw]

variable [CompleteSpace H]

/-- The proved algebraic isometry extends to the same literal stock tensor completion. -/
def tensorToLpEmbedding :
    UniformSpace.Completion ((Lp 𝕜 2 μ) ⊗[𝕜] H) →ₗᵢ[𝕜] Lp H 2 μ :=
  ((tensorToLpLinearMap μ).isometryOfInner (tensorToLpLinearMap_inner μ)).fromCompletion

/-- The extension retains every algebraic tensor value. -/
theorem tensorToLpEmbedding_coe (z : (Lp 𝕜 2 μ) ⊗[𝕜] H) :
    tensorToLpEmbedding μ (z : UniformSpace.Completion ((Lp 𝕜 2 μ) ⊗[𝕜] H)) =
      tensorToLpLinearMap μ z :=
  LinearIsometry.fromCompletion_apply_coe _ z

/-- The actual completed scalar L2 Hilbert tensor is canonically the actual vector-valued L2 space. -/
def tensorToLp : UniformSpace.Completion ((Lp 𝕜 2 μ) ⊗[𝕜] H) ≃ₗᵢ[𝕜] Lp H 2 μ := by
  let I := tensorToLpEmbedding (𝕜 := 𝕜) (H := H) μ
  have hclosed : IsClosed (Set.range I) := I.isometry.isClosedEmbedding.isClosed_range
  have hsurj : Function.Surjective I := by
    apply Lp.induction (p := 2) (by simp) (fun f => ∃ z, I z = f)
    · intro x s hs hμs
      refine ⟨((indicatorConstLp 2 hs hμs.ne (1 : 𝕜)) ⊗ₜ[𝕜] x :
        UniformSpace.Completion ((Lp 𝕜 2 μ) ⊗[𝕜] H)), ?_⟩
      change tensorToLpEmbedding μ
          (((indicatorConstLp 2 hs hμs.ne (1 : 𝕜)) ⊗ₜ[𝕜] x) :
            UniformSpace.Completion ((Lp 𝕜 2 μ) ⊗[𝕜] H)) =
        (Lp.simpleFunc.indicatorConst 2 hs hμs.ne x : Lp H 2 μ)
      rw [tensorToLpEmbedding_coe]
      change (ContinuousLinearMap.toSpanSingleton 𝕜 x).compLp
          (indicatorConstLp 2 hs hμs.ne (1 : 𝕜)) = indicatorConstLp 2 hs hμs.ne x
      apply Lp.ext
      have hscalar : indicatorConstLp 2 hs hμs.ne (1 : 𝕜) =ᵐ[μ]
          s.indicator (fun _ => (1 : 𝕜)) := indicatorConstLp_coeFn
      have hvector : indicatorConstLp 2 hs hμs.ne x =ᵐ[μ]
          s.indicator (fun _ => x) := indicatorConstLp_coeFn
      filter_upwards [(ContinuousLinearMap.toSpanSingleton 𝕜 x).coeFn_compLp
        (indicatorConstLp 2 hs hμs.ne (1 : 𝕜)), hscalar, hvector] with a hmap ha hx
      rw [hmap, ha, hx, ContinuousLinearMap.toSpanSingleton_apply]
      by_cases h : a ∈ s <;> simp [h]
    · intro _f _g _hf _hg _hdisjoint hfx hgy
      obtain ⟨x, hx⟩ := hfx
      obtain ⟨y, hy⟩ := hgy
      exact ⟨x + y, by rw [map_add, hx, hy]⟩
    · exact hclosed
  exact LinearIsometryEquiv.ofSurjective I hsurj

/-- Every completed pure tensor has the exact computed scalar-vector Lp value. -/
@[simp]
theorem tensorToLp_tmul (f : Lp 𝕜 2 μ) (x : H) :
    tensorToLp μ ((f ⊗ₜ[𝕜] x : (Lp 𝕜 2 μ) ⊗[𝕜] H) :
        UniformSpace.Completion ((Lp 𝕜 2 μ) ⊗[𝕜] H)) =
      (ContinuousLinearMap.toSpanSingleton 𝕜 x).compLp f := by
  change tensorToLpEmbedding μ ((f ⊗ₜ[𝕜] x : (Lp 𝕜 2 μ) ⊗[𝕜] H) :
    UniformSpace.Completion ((Lp 𝕜 2 μ) ⊗[𝕜] H)) = _
  rw [tensorToLpEmbedding_coe]
  rfl

/-- The completed pure-tensor comparison retains the original pointwise formula almost everywhere. -/
theorem tensorToLp_tmul_ae (f : Lp 𝕜 2 μ) (x : H) :
    tensorToLp μ ((f ⊗ₜ[𝕜] x : (Lp 𝕜 2 μ) ⊗[𝕜] H) :
        UniformSpace.Completion ((Lp 𝕜 2 μ) ⊗[𝕜] H)) =ᵐ[μ] fun s => f s • x := by
  rw [tensorToLp_tmul]
  exact (ContinuousLinearMap.toSpanSingleton 𝕜 x).coeFn_compLp f

end

end MeasureTheory.L2
