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

public import MathlibExt.MeasureTheory.Function.L2Space.TensorProduct

/-!
# Hilbert-first scalar L² tensor equivalence

Let X be a measurable space, μ any measure on X, 𝕜 an RCLike scalar field and H an inner
product space over 𝕜. Write L²_𝕜=L²(X,μ;𝕜) and L²_H=L²(X,μ;H), with their L² norms. Assume H
is complete. The completed Hilbert tensor H⊗̂L²_𝕜 is 𝕜-linearly isometrically equivalent to
L²_H by x⊗f↦(s↦f(s)•x).
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
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (μ : Measure X)

/-- **Isometric equivalence from the Hilbert-first L² tensor.**

Let X be a measurable space, μ any measure on X, 𝕜 an RCLike scalar field and H an inner
product space over 𝕜. Write L²_𝕜=L²(X,μ;𝕜) and L²_H=L²(X,μ;H), with their L² norms. Assume H
is complete. The map tensorToLpRight μ:H⊗̂L²_𝕜≃ₗᵢ[𝕜]L²_H sends x⊗f to the L² class of
s↦f(s)•x.
-/
def tensorToLpRight : UniformSpace.Completion (H ⊗[𝕜] (Lp 𝕜 2 μ)) ≃ₗᵢ[𝕜] Lp H 2 μ := by
  let c := TensorProduct.commIsometry 𝕜 H (Lp 𝕜 2 μ)
  let f := c.toLinearIsometry.completion
  let g := c.symm.toLinearIsometry.completion
  have hfg : f.toLinearMap.comp g.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro z
    change f (g z) = z
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (f.continuous.comp g.continuous) continuous_id) ?_
    intro z
    change c.toLinearIsometry.completion
        (c.symm.toLinearIsometry.completion
          (z : UniformSpace.Completion ((Lp 𝕜 2 μ) ⊗[𝕜] H))) =
      (z : UniformSpace.Completion ((Lp 𝕜 2 μ) ⊗[𝕜] H))
    rw [LinearIsometry.completion_apply_coe, LinearIsometry.completion_apply_coe]
    exact congrArg (fun z : (Lp 𝕜 2 μ) ⊗[𝕜] H =>
      (z : UniformSpace.Completion ((Lp 𝕜 2 μ) ⊗[𝕜] H))) (c.apply_symm_apply z)
  have hgf : g.toLinearMap.comp f.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro z
    change g (f z) = z
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (g.continuous.comp f.continuous) continuous_id) ?_
    intro z
    change c.symm.toLinearIsometry.completion
        (c.toLinearIsometry.completion
          (z : UniformSpace.Completion (H ⊗[𝕜] (Lp 𝕜 2 μ)))) =
      (z : UniformSpace.Completion (H ⊗[𝕜] (Lp 𝕜 2 μ)))
    rw [LinearIsometry.completion_apply_coe, LinearIsometry.completion_apply_coe]
    exact congrArg (fun z : H ⊗[𝕜] (Lp 𝕜 2 μ) =>
      (z : UniformSpace.Completion (H ⊗[𝕜] (Lp 𝕜 2 μ)))) (c.symm_apply_apply z)
  let E := LinearIsometryEquiv.ofLinearIsometry f g.toLinearMap hfg hgf
  exact E.trans (tensorToLp (𝕜 := 𝕜) (H := H) μ)

/-- **Hilbert-first pure tensor formula almost everywhere.**

Let X be a measurable space, μ any measure on X, 𝕜 an RCLike scalar field and H an inner
product space over 𝕜. Write L²_𝕜=L²(X,μ;𝕜) and L²_H=L²(X,μ;H), with their L² norms. Assume H
is complete. For x∈H and f∈L²_𝕜, tensorToLpRight μ (x⊗f) equals s↦f(s)•x μ-almost everywhere.
-/
theorem tensorToLpRight_tmul_ae (x : H) (f : Lp 𝕜 2 μ) :
    tensorToLpRight μ ((x ⊗ₜ[𝕜] f : H ⊗[𝕜] (Lp 𝕜 2 μ)) :
        UniformSpace.Completion (H ⊗[𝕜] (Lp 𝕜 2 μ))) =ᵐ[μ] fun s => f s • x := by
  change tensorToLp μ
      ((TensorProduct.commIsometry 𝕜 H (Lp 𝕜 2 μ)).toLinearIsometry.completion
        ((x ⊗ₜ[𝕜] f : H ⊗[𝕜] (Lp 𝕜 2 μ)) :
          UniformSpace.Completion (H ⊗[𝕜] (Lp 𝕜 2 μ)))) =ᵐ[μ] _
  rw [LinearIsometry.completion_apply_coe]
  change tensorToLp μ
      ((f ⊗ₜ[𝕜] x : (Lp 𝕜 2 μ) ⊗[𝕜] H) :
        UniformSpace.Completion ((Lp 𝕜 2 μ) ⊗[𝕜] H)) =ᵐ[μ] _
  exact tensorToLp_tmul_ae μ f x

end

end MeasureTheory.L2
