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
# Normality from pullback of vector functionals

Let `f : M → N` be a unital complex star homomorphism between concrete von Neumann algebras. If
every target vector functional `x ↦ ⟨ξ,f(x)η⟩` belongs to the source normal-functional space
`M_*`, then `f` is ultraweakly continuous and defines a normal homomorphism.

The criterion uses vector functionals on the complete target Hilbert space and the norm-closed
source predual span. Injectivity is not required.
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

/-- **Normal homomorphism from normal vector-functional pullbacks.** Let `M,N` be concrete von
Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. let `f : M →⋆ₐ[ℂ] N` and suppose `vectorFunctional N ξ η ∘ f ∈
M_*` for every `ξ,η` in the target Hilbert space. Then `ofVectorFunctionalPullbacks f`
bundles this star map as an ultraweakly continuous normal homomorphism. -/
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
