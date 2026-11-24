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
# Actual completion of a linear isometry equivalence

Complete the original forward and inverse stock isometries. Dense original
coefficients and continuity prove their inverse laws on the full completions.
The actual maps and norms are retained, with independent universes and zero
spaces allowed. This supplies completion of the actual tensor congruence and
associator used by the original mixed-factor Radon product constructor.
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

/-- Complete an actual linear isometry equivalence using its stock forward and inverse completion maps. -/
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

/-- The actual completed equivalence retains the literal original coefficient value. -/
theorem completion_apply_coe (e : E ≃ₗᵢ[𝕜] F) (z : E) :
    completion e (z : Completion E) = (e z : Completion F) := by
  let _ : UniformContinuousConstSMul 𝕜 E :=
    uniformContinuousConstSMul_of_continuousConstSMul 𝕜 E
  let _ : UniformContinuousConstSMul 𝕜 F :=
    uniformContinuousConstSMul_of_continuousConstSMul 𝕜 F
  change e.toLinearIsometry.completion (z : Completion E) = (e z : Completion F)
  exact LinearIsometry.completion_apply_coe _ _

/-- The inverse completed equivalence retains the literal original inverse coefficient value. -/
theorem completion_symm_apply_coe (e : E ≃ₗᵢ[𝕜] F) (z : F) :
    (completion e).symm (z : Completion F) = (e.symm z : Completion E) := by
  let _ : UniformContinuousConstSMul 𝕜 E :=
    uniformContinuousConstSMul_of_continuousConstSMul 𝕜 E
  let _ : UniformContinuousConstSMul 𝕜 F :=
    uniformContinuousConstSMul_of_continuousConstSMul 𝕜 F
  change e.symm.toLinearIsometry.completion (z : Completion F) = (e.symm z : Completion E)
  exact LinearIsometry.completion_apply_coe _ _


/-- The actual completed equivalence has the stock forward completion linear-map DATA. -/
theorem completion_toLinearMap (e : E ≃ₗᵢ[𝕜] F) :
    letI : UniformContinuousConstSMul 𝕜 E :=
      uniformContinuousConstSMul_of_continuousConstSMul 𝕜 E
    letI : UniformContinuousConstSMul 𝕜 F :=
      uniformContinuousConstSMul_of_continuousConstSMul 𝕜 F
    (e.completion).toLinearMap = e.toLinearIsometry.completion.toLinearMap := rfl

/-- The actual inverse completed equivalence has the stock inverse completion linear-map DATA. -/
theorem completion_symm_toLinearMap (e : E ≃ₗᵢ[𝕜] F) :
    letI : UniformContinuousConstSMul 𝕜 E :=
      uniformContinuousConstSMul_of_continuousConstSMul 𝕜 E
    letI : UniformContinuousConstSMul 𝕜 F :=
      uniformContinuousConstSMul_of_continuousConstSMul 𝕜 F
    (e.completion).symm.toLinearMap = e.symm.toLinearIsometry.completion.toLinearMap := rfl

end

end LinearIsometryEquiv
