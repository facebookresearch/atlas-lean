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
# The dual of normal-functional pullback is the normal algebra map

For a normal unital complex star homomorphism `f : M → N`, let `B : N_* → M_*` be the pullback
`φ ↦ φ∘f`. Its bounded dual is `B*(F)=F∘B`.

Let `J_M(x)(φ)=φ(x)` and `J_N(y)(ψ)=ψ(y)` be the evaluation identifications with the duals of
the normal-functional Banach spaces. Then `B*(J_M(x))=J_N(f(x))` for every `x ∈ M`. Injectivity
of `f` is not required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra.NormalStarAlgHom

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- **Dual pullback agrees with the algebra map under evaluation.** Let `M,N` be concrete von
Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. let `B=f.predualPullback`, `B*(F)=F∘B`, and `J_M(x)(φ)=φ(x)`,
`J_N(y)(ψ)=ψ(y)`. For every `x ∈ M`, `B*(J_M(x))=J_N(f(x))` in `(N_*)*`. -/
theorem predualPullback_dual_evaluation (f : NormalStarAlgHom M N) (x : M) :
    ((ContinuousLinearMap.compL ℂ (normalFunctionalSpace N) (normalFunctionalSpace M) ℂ).flip
      f.predualPullback) (normalFunctionalEvaluationEquiv M x) =
        normalFunctionalEvaluationEquiv N (f x) := by
  apply ContinuousLinearMap.ext
  intro φ
  change normalFunctionalEvaluationEquiv M x (f.predualPullback φ) =
    normalFunctionalEvaluationEquiv N (f x) φ
  rw [normalFunctionalEvaluationEquiv_apply, normalFunctionalEvaluationEquiv_apply,
    f.predualPullback_apply]

end

end VonNeumannAlgebra.NormalStarAlgHom
