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
# Scalar L² tensors and Hilbert-valued L² functions

Let X be a measurable space, μ any measure on X, 𝕜 an RCLike scalar field and H an inner
product space over 𝕜. Write L²_𝕜=L²(X,μ;𝕜) and L²_H=L²(X,μ;H), with their L² norms. The
scalar-vector bilinear map b:L²_𝕜×H→L²_H sends (f,x) to the class of s↦f(s)•x. Its algebraic
tensor map preserves inner products. When H is complete, it extends to a linear isometric
equivalence L²_𝕜⊗̂H≃L²_H sending f⊗x to s↦f(s)•x. The measure μ is arbitrary and the space
universes are independent.
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

/-- **Scalar-vector bilinear map into L².**

Let X be a measurable space, μ any measure on X, 𝕜 an RCLike scalar field and H an inner
product space over 𝕜. Write L²_𝕜=L²(X,μ;𝕜) and L²_H=L²(X,μ;H), with their L² norms. The
scalar-vector bilinear map b:L²_𝕜×H→L²_H sends (f,x) to the class of s↦f(s)•x. The bounded
bilinear map scalarVector μ:L²_𝕜→L[𝕜](H→L[𝕜]L²_H) has these values.
-/
def scalarVector : Lp 𝕜 2 μ →L[𝕜] H →L[𝕜] Lp H 2 μ :=
  ((ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] H →L[𝕜] H).flip.compLpL₂ 2 μ).flip

/-- **Almost-everywhere scalar-vector L² formula.**

Let X be a measurable space, μ any measure on X, 𝕜 an RCLike scalar field and H an inner
product space over 𝕜. Write L²_𝕜=L²(X,μ;𝕜) and L²_H=L²(X,μ;H), with their L² norms. The
scalar-vector bilinear map b:L²_𝕜×H→L²_H sends (f,x) to the class of s↦f(s)•x. For f∈L²_𝕜 and
x∈H, scalarVector μ f x equals s↦f(s)•x μ-almost everywhere.
-/
theorem scalarVector_ae_eq (f : Lp 𝕜 2 μ) (x : H) :
    scalarVector μ f x =ᵐ[μ] fun s => f s • x := by
  change (ContinuousLinearMap.toSpanSingleton 𝕜 x).compLp f =ᵐ[μ] fun s => f s • x
  exact (ContinuousLinearMap.toSpanSingleton 𝕜 x).coeFn_compLp f

/-- **Inner product of scalar-vector L² functions.**

Let X be a measurable space, μ any measure on X, 𝕜 an RCLike scalar field and H an inner
product space over 𝕜. Write L²_𝕜=L²(X,μ;𝕜) and L²_H=L²(X,μ;H), with their L² norms. The
scalar-vector bilinear map b:L²_𝕜×H→L²_H sends (f,x) to the class of s↦f(s)•x. For f,g∈L²_𝕜
and x,y∈H, ⟪b(f,x),b(g,y)⟫_𝕜=⟪f,g⟫_𝕜⟪x,y⟫_𝕜.
-/
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

/-- **Algebraic tensor map to vector-valued L².**

Let X be a measurable space, μ any measure on X, 𝕜 an RCLike scalar field and H an inner
product space over 𝕜. Write L²_𝕜=L²(X,μ;𝕜) and L²_H=L²(X,μ;H), with their L² norms. The
scalar-vector bilinear map b:L²_𝕜×H→L²_H sends (f,x) to the class of s↦f(s)•x. The 𝕜-linear
map tensorToLpLinearMap μ:L²_𝕜⊗H→L²_H sends f⊗x to b(f,x), the L² class of s↦f(s)•x.
-/
def tensorToLpLinearMap : (Lp 𝕜 2 μ) ⊗[𝕜] H →ₗ[𝕜] Lp H 2 μ :=
  TensorProduct.lift (scalarVector μ).toLinearMap₁₂

/-- **Value of the algebraic L² tensor map on a pure tensor.**

Let X be a measurable space, μ any measure on X, 𝕜 an RCLike scalar field and H an inner
product space over 𝕜. Write L²_𝕜=L²(X,μ;𝕜) and L²_H=L²(X,μ;H), with their L² norms. For f∈L²_𝕜
and x∈H, tensorToLpLinearMap μ (f⊗x) is the L² image of f under the bounded linear map z↦z•x
from 𝕜 to H.
-/
@[simp]
theorem tensorToLpLinearMap_tmul (f : Lp 𝕜 2 μ) (x : H) :
    tensorToLpLinearMap μ (f ⊗ₜ[𝕜] x) = (ContinuousLinearMap.toSpanSingleton 𝕜 x).compLp f := by
  change TensorProduct.lift (scalarVector μ).toLinearMap₁₂ (f ⊗ₜ[𝕜] x) = _
  rw [TensorProduct.lift.tmul]
  rfl

/-- **Algebraic L² tensor map preserves inner products.**

Let X be a measurable space, μ any measure on X, 𝕜 an RCLike scalar field and H an inner
product space over 𝕜. Write L²_𝕜=L²(X,μ;𝕜) and L²_H=L²(X,μ;H), with their L² norms. For
J0=tensorToLpLinearMap μ:L²_𝕜⊗H→L²_H and algebraic tensors z,w, ⟪J0(z),J0(w)⟫_𝕜=⟪z,w⟫_𝕜, using
the inner-product tensor structure.
-/
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

/-- **Completed scalar L² tensor embedding.**

Let X be a measurable space, μ any measure on X, 𝕜 an RCLike scalar field and H an inner
product space over 𝕜. Write L²_𝕜=L²(X,μ;𝕜) and L²_H=L²(X,μ;H), with their L² norms. The
scalar-vector bilinear map b:L²_𝕜×H→L²_H sends (f,x) to the class of s↦f(s)•x. Assume H is
complete, so L²_H is a Hilbert space. Let J:L²_𝕜⊗̂H→L²_H be the completed linear isometry
extending b on pure tensors. The map tensorToLpEmbedding μ is J, with domain the Hilbert
tensor completion L²_𝕜⊗̂H and the L² norm on its codomain.
-/
def tensorToLpEmbedding :
    UniformSpace.Completion ((Lp 𝕜 2 μ) ⊗[𝕜] H) →ₗᵢ[𝕜] Lp H 2 μ :=
  ((tensorToLpLinearMap μ).isometryOfInner (tensorToLpLinearMap_inner μ)).fromCompletion

/-- **Completed L² tensor embedding on an algebraic tensor.**

Let X be a measurable space, μ any measure on X, 𝕜 an RCLike scalar field and H an inner
product space over 𝕜. Write L²_𝕜=L²(X,μ;𝕜) and L²_H=L²(X,μ;H), with their L² norms. The
scalar-vector bilinear map b:L²_𝕜×H→L²_H sends (f,x) to the class of s↦f(s)•x. Assume H is
complete, so L²_H is a Hilbert space. Let J:L²_𝕜⊗̂H→L²_H be the completed linear isometry
extending b on pure tensors. If z∈L²_𝕜⊗H and ι denotes its canonical inclusion into L²_𝕜⊗̂H,
tensorToLpEmbedding μ (ι(z))=tensorToLpLinearMap μ z. In particular, ι(f⊗x) maps to the class
s↦f(s)•x.
-/
theorem tensorToLpEmbedding_coe (z : (Lp 𝕜 2 μ) ⊗[𝕜] H) :
    tensorToLpEmbedding μ (z : UniformSpace.Completion ((Lp 𝕜 2 μ) ⊗[𝕜] H)) =
      tensorToLpLinearMap μ z :=
  LinearIsometry.fromCompletion_apply_coe _ z

/-- **Isometric equivalence with Hilbert-valued L².**

Let X be a measurable space, μ any measure on X, 𝕜 an RCLike scalar field and H an inner
product space over 𝕜. Write L²_𝕜=L²(X,μ;𝕜) and L²_H=L²(X,μ;H), with their L² norms. Assume H
is complete. The 𝕜-linear isometric equivalence tensorToLp μ:L²_𝕜⊗̂H≃ₗᵢ[𝕜]L²_H sends completed
pure tensors f⊗x to the L² class s↦f(s)•x.
-/
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

/-- **Pure tensor value of the L² equivalence.**

Let X be a measurable space, μ any measure on X, 𝕜 an RCLike scalar field and H an inner
product space over 𝕜. Write L²_𝕜=L²(X,μ;𝕜) and L²_H=L²(X,μ;H), with their L² norms. Assume H
is complete. For f∈L²_𝕜 and x∈H, tensorToLp μ applied to the completed pure tensor f⊗x is the
L² image of f under z↦z•x.
-/
@[simp]
theorem tensorToLp_tmul (f : Lp 𝕜 2 μ) (x : H) :
    tensorToLp μ ((f ⊗ₜ[𝕜] x : (Lp 𝕜 2 μ) ⊗[𝕜] H) :
        UniformSpace.Completion ((Lp 𝕜 2 μ) ⊗[𝕜] H)) =
      (ContinuousLinearMap.toSpanSingleton 𝕜 x).compLp f := by
  change tensorToLpEmbedding μ ((f ⊗ₜ[𝕜] x : (Lp 𝕜 2 μ) ⊗[𝕜] H) :
    UniformSpace.Completion ((Lp 𝕜 2 μ) ⊗[𝕜] H)) = _
  rw [tensorToLpEmbedding_coe]
  rfl

/-- **Almost-everywhere value of the completed L² tensor equivalence.**

Let X be a measurable space, μ any measure on X, 𝕜 an RCLike scalar field and H an inner
product space over 𝕜. Write L²_𝕜=L²(X,μ;𝕜) and L²_H=L²(X,μ;H), with their L² norms. Assume H
is complete. For f∈L²_𝕜 and x∈H, tensorToLp μ (f⊗x) equals the function s↦f(s)•x μ-almost
everywhere.
-/
theorem tensorToLp_tmul_ae (f : Lp 𝕜 2 μ) (x : H) :
    tensorToLp μ ((f ⊗ₜ[𝕜] x : (Lp 𝕜 2 μ) ⊗[𝕜] H) :
        UniformSpace.Completion ((Lp 𝕜 2 μ) ⊗[𝕜] H)) =ᵐ[μ] fun s => f s • x := by
  rw [tensorToLp_tmul]
  exact (ContinuousLinearMap.toSpanSingleton 𝕜 x).coeFn_compLp f

end

end MeasureTheory.L2
