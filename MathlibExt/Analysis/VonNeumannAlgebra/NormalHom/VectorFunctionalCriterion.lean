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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom

/-!
# Normal homomorphisms from actual vector-functional pullbacks

Norm-continuous functional precomposition preserves the closed span once
it preserves every original vector functional. The evaluation-induced
ultraweak topology then gives the normality of the same algebra map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra

namespace VonNeumannAlgebra.NormalStarAlgHom

noncomputable section

universe uH uK

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- The literal star map is normal when its computed vector pullbacks lie in the actual source predual. -/
def ofVectorFunctionalPullbacks (f : M →⋆ₐ[ℂ] N)
    (hvec : ∀ ξ η : K, (vectorFunctional N ξ η).comp
      (⟨LinearMap.ofClass f, map_continuous f⟩ : M →L[ℂ] N) ∈ normalFunctionalSpace M) :
    NormalStarAlgHom M N where
  toStarAlgHom := f
  continuous_ultraweak := by
    let F : M →L[ℂ] N := ⟨LinearMap.ofClass f, map_continuous f⟩
    let B : StrongDual ℂ N →L[ℂ] StrongDual ℂ M := (ContinuousLinearMap.compL ℂ M N ℂ).flip F
    let P : Submodule ℂ (StrongDual ℂ N) := (normalFunctionalSpace M).comap B.toLinearMap
    have hP : IsClosed (P : Set (StrongDual ℂ N)) :=
      (normalFunctionalSpace_isClosed M).preimage B.continuous
    have hNP : normalFunctionalSpace N ≤ P := by
      apply normalFunctionalSpace_le N hP
      intro ξ η
      exact hvec ξ η
    apply (ultraweak_continuous_iff N).2
    intro φ
    let ψ : normalFunctionalSpace M := ⟨B (φ : StrongDual ℂ N), hNP φ.property⟩
    have hfun :
        (fun x : Ultraweak M => (φ : StrongDual ℂ N)
          (ultraweakLinearEquiv N ((ultraweakLinearEquiv N).symm (f (ultraweakLinearEquiv M x))))) =
        (fun x : Ultraweak M => (ψ : StrongDual ℂ M) (ultraweakLinearEquiv M x)) := by
      funext x
      rw [LinearEquiv.apply_symm_apply]
      rfl
    rw [hfun]
    exact ultraweak_eval_continuous M ψ

end

end VonNeumannAlgebra.NormalStarAlgHom
