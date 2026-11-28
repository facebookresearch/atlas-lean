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
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Dense spans of pure tensors from dense factor sets

Let H,K be inner product spaces over an RCLike field 𝕜, and s⊆H, t⊆K have dense 𝕜-linear
spans. Then the completed pure tensors {x⊗y:x∈s,y∈t} have dense linear span in the Hilbert
tensor completion H⊗̂K.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open UniformSpace Set
open scoped TensorProduct

namespace TensorProduct

universe u𝕜 uH uK

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

/-- **Dense factor spans generate a dense completed tensor span.**

Let H,K be inner product spaces over an RCLike field 𝕜 in independent universes. If span_𝕜(s)
is dense in H and span_𝕜(t) dense in K, then span_𝕜{x⊗y:x∈s,y∈t} is dense in the completion
H⊗̂K of the inner-product tensor norm.
-/
theorem dense_span_completed_tmul (s : Set H) (t : Set K)
    (hs : Dense (Submodule.span 𝕜 s : Set H))
    (ht : Dense (Submodule.span 𝕜 t : Set K)) :
    Dense (Submodule.span 𝕜
      {z : Completion (H ⊗[𝕜] K) | ∃ x ∈ s, ∃ y ∈ t,
        z = (x ⊗ₜ[𝕜] y : Completion (H ⊗[𝕜] K))} : Set (Completion (H ⊗[𝕜] K))) := by
  let S : Submodule 𝕜 (Completion (H ⊗[𝕜] K)) := Submodule.span 𝕜
    {z : Completion (H ⊗[𝕜] K) | ∃ x ∈ s, ∃ y ∈ t,
      z = (x ⊗ₜ[𝕜] y : Completion (H ⊗[𝕜] K))}
  have hSpan {x : H} {y : K} (hx : x ∈ Submodule.span 𝕜 s)
      (hy : y ∈ Submodule.span 𝕜 t) :
      (x ⊗ₜ[𝕜] y : Completion (H ⊗[𝕜] K)) ∈ S.topologicalClosure := by
    refine Submodule.span_induction₂
      (p := fun x y _ _ =>
        (x ⊗ₜ[𝕜] y : Completion (H ⊗[𝕜] K)) ∈ S.topologicalClosure)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    · intro x y hx hy
      exact S.le_topologicalClosure (Submodule.subset_span ⟨x, hx, y, hy, rfl⟩)
    · intro y _hy
      simpa only [zero_tmul, Completion.coe_zero] using S.topologicalClosure.zero_mem
    · intro x _hx
      simpa only [tmul_zero, Completion.coe_zero] using S.topologicalClosure.zero_mem
    · intro x y z _hx _hy _hz hx hy
      simpa only [add_tmul, Completion.coe_add] using S.topologicalClosure.add_mem hx hy
    · intro x y z _hx _hy _hz hy hz
      simpa only [tmul_add, Completion.coe_add] using S.topologicalClosure.add_mem hy hz
    · intro c x y _hx _hy hxy
      simpa only [← smul_tmul', Completion.coe_smul] using
        S.topologicalClosure.smul_mem c hxy
    · intro c x y _hx _hy hxy
      simpa only [tmul_smul, Completion.coe_smul] using
        S.topologicalClosure.smul_mem c hxy
  have hLeft (y : K) (hy : y ∈ Submodule.span 𝕜 t) (x : H) :
      (x ⊗ₜ[𝕜] y : Completion (H ⊗[𝕜] K)) ∈ S.topologicalClosure := by
    have hc : Continuous fun x : H => (x ⊗ₜ[𝕜] y : Completion (H ⊗[𝕜] K)) :=
      (Completion.continuous_coe (H ⊗[𝕜] K)).comp
        ((continuous_tmul (𝕜 := 𝕜) (E := H) (F := K)).comp
          (continuous_id.prodMk continuous_const))
    exact hs.induction (fun x hx => hSpan hx hy)
      (S.isClosed_topologicalClosure.preimage hc) x
  have hPure (x : H) (y : K) :
      (x ⊗ₜ[𝕜] y : Completion (H ⊗[𝕜] K)) ∈ S.topologicalClosure := by
    have hc : Continuous fun y : K => (x ⊗ₜ[𝕜] y : Completion (H ⊗[𝕜] K)) :=
      (Completion.continuous_coe (H ⊗[𝕜] K)).comp
        ((continuous_tmul (𝕜 := 𝕜) (E := H) (F := K)).comp
          (continuous_const.prodMk continuous_id))
    exact ht.induction (fun y hy => hLeft y hy x)
      (S.isClosed_topologicalClosure.preimage hc) y
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.eq_top_iff'.mpr
  intro z
  refine Completion.induction_on z S.isClosed_topologicalClosure ?_
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul x y => exact hPure x y
  | add w v hw hv =>
    simpa only [Completion.coe_add] using S.topologicalClosure.add_mem hw hv

end TensorProduct
