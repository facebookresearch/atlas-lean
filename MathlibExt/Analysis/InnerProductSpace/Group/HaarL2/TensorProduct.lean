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

public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.Completion
public import MathlibExt.MeasureTheory.Function.L2Space.TensorProduct

/-!
# Scalar compact-support L² completion tensored with a Hilbert space

Let `G` be an R₁ locally compact Borel space, `μ` a regular measure and `H` a complete complex
Hilbert space. The scalar separated L² completion `C_μ` of `C_c(G,ℂ)` identifies with `Lp ℂ 2
μ`.

The completed tensor with scalar factor first gives `Completion(C_μ ⊗[ℂ] H) ≃ Lp H 2 μ`, sending
`f⊗ξ` to `s ↦ J_μ(f)(s) • ξ`. No group structure, Haar condition or nonzero-space hypothesis is
required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped TensorProduct ENNReal InnerProductSpace

namespace MeasureTheory.HaarL2

noncomputable section

universe uG uH

variable {G : Type uG} [TopologicalSpace G] [R1Space G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.Regular]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Isometric scalar-completion-first tensor realization of L².** Let `G` be an R₁ locally
compact Borel space, `μ` a regular measure and `H` a complete complex Hilbert space. Let
`C_μ` be the separated L² completion of `C_c(G,ℂ)` and `J_μ : C_μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ` its
scalar comparison. `completionTensorToLp μ : Completion(C_μ ⊗[ℂ] H) ≃ₗᵢ[ℂ] Lp H 2 μ` sends
`f⊗ξ` to `s ↦ J_μ(f)(s) • ξ`. -/
def completionTensorToLp :
    UniformSpace.Completion ((CompletionCore (H := ℂ) μ) ⊗[ℂ] H) ≃ₗᵢ[ℂ] Lp H 2 μ := by
  let e := TensorProduct.congrIsometry (completionToLp (H := ℂ) μ) (LinearIsometryEquiv.refl ℂ H)
  let f := e.toLinearIsometry.completion
  let g := e.symm.toLinearIsometry.completion
  have hfg : f.toLinearMap.comp g.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro z
    change f (g z) = z
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (f.continuous.comp g.continuous) continuous_id) ?_
    intro z
    change e.toLinearIsometry.completion
        (e.symm.toLinearIsometry.completion
          (z : UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] H))) =
      (z : UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] H))
    rw [LinearIsometry.completion_apply_coe, LinearIsometry.completion_apply_coe]
    exact congrArg (fun z : (Lp ℂ 2 μ) ⊗[ℂ] H =>
      (z : UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] H))) (e.apply_symm_apply z)
  have hgf : g.toLinearMap.comp f.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro z
    change g (f z) = z
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (g.continuous.comp f.continuous) continuous_id) ?_
    intro z
    change e.symm.toLinearIsometry.completion
        (e.toLinearIsometry.completion
          (z : UniformSpace.Completion ((CompletionCore (H := ℂ) μ) ⊗[ℂ] H))) =
      (z : UniformSpace.Completion ((CompletionCore (H := ℂ) μ) ⊗[ℂ] H))
    rw [LinearIsometry.completion_apply_coe, LinearIsometry.completion_apply_coe]
    exact congrArg (fun z : (CompletionCore (H := ℂ) μ) ⊗[ℂ] H =>
      (z : UniformSpace.Completion ((CompletionCore (H := ℂ) μ) ⊗[ℂ] H))) (e.symm_apply_apply z)
  let E := LinearIsometryEquiv.ofLinearIsometry f g.toLinearMap hfg hgf
  exact E.trans (L2.tensorToLp (𝕜 := ℂ) (H := H) μ)

/-- **Almost-everywhere pure tensor formula of the scalar completion comparison.** Let `G` be
an R₁ locally compact Borel space, `μ` a regular measure and `H` a complete complex
Hilbert space. Let `C_μ` be the separated L² completion of `C_c(G,ℂ)` and `J_μ : C_μ
≃ₗᵢ[ℂ] Lp ℂ 2 μ` its scalar comparison. for `f∈C_μ`, `ξ∈H`, the image of `f⊗ξ` is almost
everywhere `s ↦ J_μ(f)(s) • ξ`. -/
theorem completionTensorToLp_tmul_ae (f : CompletionCore (H := ℂ) μ) (x : H) :
    completionTensorToLp μ ((f ⊗ₜ[ℂ] x : (CompletionCore (H := ℂ) μ) ⊗[ℂ] H) :
        UniformSpace.Completion ((CompletionCore (H := ℂ) μ) ⊗[ℂ] H)) =ᵐ[μ]
      fun s => completionToLp (H := ℂ) μ f s • x := by
  change L2.tensorToLp μ
      ((TensorProduct.congrIsometry (completionToLp (H := ℂ) μ)
          (LinearIsometryEquiv.refl ℂ H)).toLinearIsometry.completion
          ((f ⊗ₜ[ℂ] x : (CompletionCore (H := ℂ) μ) ⊗[ℂ] H) :
            UniformSpace.Completion ((CompletionCore (H := ℂ) μ) ⊗[ℂ] H))) =ᵐ[μ] _
  rw [LinearIsometry.completion_apply_coe]
  change L2.tensorToLp μ
      (((completionToLp (H := ℂ) μ f) ⊗ₜ[ℂ] x : (Lp ℂ 2 μ) ⊗[ℂ] H) :
        UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] H)) =ᵐ[μ] _
  exact L2.tensorToLp_tmul_ae μ (completionToLp (H := ℂ) μ f) x

end

end MeasureTheory.HaarL2
