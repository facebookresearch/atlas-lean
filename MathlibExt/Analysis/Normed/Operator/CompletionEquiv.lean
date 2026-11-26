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

public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Completion of a linear isometric equivalence

For normed spaces `E,F` over a normed field `𝕜`, a linear isometric equivalence `e : E ≃ₗᵢ[𝕜] F`
extends to a linear isometric equivalence `ê : Completion E ≃ₗᵢ[𝕜] Completion F`.

On the dense inclusions it satisfies `ê(ι_E x)=ι_F(e x)` and `ê⁻¹(ι_F y)=ι_E(e⁻¹y)`. Its forward
and inverse linear maps are the completed forward and inverse isometries. Neither
coefficient-space completeness nor nonzero spaces are required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open UniformSpace

namespace LinearIsometryEquiv

noncomputable section

universe u𝕜 uE uF

variable {𝕜 : Type u𝕜} [NormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Completed linear isometric equivalence.** Let `𝕜` be a normed field, `E,F` normed
`𝕜`-spaces in independent universes, and `e : E ≃ₗᵢ[𝕜] F` a linear isometric equivalence.
`e.completion : Completion E ≃ₗᵢ[𝕜] Completion F` is the isometric extension satisfying
`ê(ι_E x)=ι_F(e x)` and inverse value `ê⁻¹(ι_F y)=ι_E(e⁻¹y)`. -/
def completion (e : E ≃ₗᵢ[𝕜] F) : Completion E ≃ₗᵢ[𝕜] Completion F := by
  let _ : UniformContinuousConstSMul 𝕜 E :=
    uniformContinuousConstSMul_of_continuousConstSMul 𝕜 E
  let _ : UniformContinuousConstSMul 𝕜 F :=
    uniformContinuousConstSMul_of_continuousConstSMul 𝕜 F
  let f := e.toLinearIsometry.completion
  let g := e.symm.toLinearIsometry.completion
  have hfg : f.toLinearMap.comp g.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro z
    change f (g z) = z
    refine Completion.induction_on z
      (isClosed_eq (f.continuous.comp g.continuous) continuous_id) ?_
    intro z
    change e.toLinearIsometry.completion
        (e.symm.toLinearIsometry.completion (z : Completion F)) = (z : Completion F)
    rw [LinearIsometry.completion_apply_coe, LinearIsometry.completion_apply_coe]
    exact congrArg (fun z : F => (z : Completion F)) (e.apply_symm_apply z)
  have hgf : g.toLinearMap.comp f.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro z
    change g (f z) = z
    refine Completion.induction_on z
      (isClosed_eq (g.continuous.comp f.continuous) continuous_id) ?_
    intro z
    change e.symm.toLinearIsometry.completion
        (e.toLinearIsometry.completion (z : Completion E)) = (z : Completion E)
    rw [LinearIsometry.completion_apply_coe, LinearIsometry.completion_apply_coe]
    exact congrArg (fun z : E => (z : Completion E)) (e.symm_apply_apply z)
  exact LinearIsometryEquiv.ofLinearIsometry f g.toLinearMap hfg hgf

/-- **Completion equivalence on a source vector.** Let `𝕜` be a normed field, `E,F` normed
`𝕜`-spaces in independent universes, and `e : E ≃ₗᵢ[𝕜] F` a linear isometric equivalence.
for `x ∈ E`, `e.completion (x : Completion E)=(e x : Completion F)`. -/
theorem completion_apply_coe (e : E ≃ₗᵢ[𝕜] F) (z : E) :
    completion e (z : Completion E) = (e z : Completion F) := by
  let _ : UniformContinuousConstSMul 𝕜 E :=
    uniformContinuousConstSMul_of_continuousConstSMul 𝕜 E
  let _ : UniformContinuousConstSMul 𝕜 F :=
    uniformContinuousConstSMul_of_continuousConstSMul 𝕜 F
  change e.toLinearIsometry.completion (z : Completion E) = (e z : Completion F)
  exact LinearIsometry.completion_apply_coe _ _

/-- **Inverse completion equivalence on a target vector.** Let `𝕜` be a normed field, `E,F`
normed `𝕜`-spaces in independent universes, and `e : E ≃ₗᵢ[𝕜] F` a linear isometric
equivalence. for `y ∈ F`, `(e.completion).symm (y : Completion F)=(e.symm y : Completion
E)`. -/
theorem completion_symm_apply_coe (e : E ≃ₗᵢ[𝕜] F) (z : F) :
    (completion e).symm (z : Completion F) = (e.symm z : Completion E) := by
  let _ : UniformContinuousConstSMul 𝕜 E :=
    uniformContinuousConstSMul_of_continuousConstSMul 𝕜 E
  let _ : UniformContinuousConstSMul 𝕜 F :=
    uniformContinuousConstSMul_of_continuousConstSMul 𝕜 F
  change e.symm.toLinearIsometry.completion (z : Completion F) = (e.symm z : Completion E)
  exact LinearIsometry.completion_apply_coe _ _


/-- **Forward linear map of the completed equivalence.** Let `𝕜` be a normed field, `E,F`
normed `𝕜`-spaces in independent universes, and `e : E ≃ₗᵢ[𝕜] F` a linear isometric
equivalence. the linear map underlying `e.completion` equals the completion of
`e.toLinearIsometry`, with value `ι_E x ↦ ι_F(e x)` on the dense domain. -/
theorem completion_toLinearMap (e : E ≃ₗᵢ[𝕜] F) :
    letI : UniformContinuousConstSMul 𝕜 E :=
      uniformContinuousConstSMul_of_continuousConstSMul 𝕜 E
    letI : UniformContinuousConstSMul 𝕜 F :=
      uniformContinuousConstSMul_of_continuousConstSMul 𝕜 F
    (e.completion).toLinearMap = e.toLinearIsometry.completion.toLinearMap := rfl

/-- **Inverse linear map of the completed equivalence.** Let `𝕜` be a normed field, `E,F`
normed `𝕜`-spaces in independent universes, and `e : E ≃ₗᵢ[𝕜] F` a linear isometric
equivalence. the linear map underlying `(e.completion).symm` equals the completion of
`e.symm.toLinearIsometry`, with value `ι_F y ↦ ι_E(e⁻¹y)`. -/
theorem completion_symm_toLinearMap (e : E ≃ₗᵢ[𝕜] F) :
    letI : UniformContinuousConstSMul 𝕜 E :=
      uniformContinuousConstSMul_of_continuousConstSMul 𝕜 E
    letI : UniformContinuousConstSMul 𝕜 F :=
      uniformContinuousConstSMul_of_continuousConstSMul 𝕜 F
    (e.completion).symm.toLinearMap = e.symm.toLinearIsometry.completion.toLinearMap := rfl

end

end LinearIsometryEquiv
