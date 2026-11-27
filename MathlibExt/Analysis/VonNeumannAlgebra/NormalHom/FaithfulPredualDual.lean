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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.PredualDualMap
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.FaithfulBallImage

/-!
# Isometric dual of the predual pullback of an injective normal map

Let `f : M → N` be an injective normal unital complex star homomorphism and `B : N_* → M_*`,
`B(φ)=φ∘f`, its predual pullback. The bounded dual map `B* : (M_*)* → (N_*)*` is `F ↦ F∘B`.

It preserves the continuous-dual norm and is an isometry. Under the evaluation identifications
`x ↦ (φ ↦ φ(x))`, this is the norm preservation of the injective C-star map `f`. No predual
quotient property is assumed.
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

/-- **Norm preserved by the dual of injective normal predual pullback.** Let `M,N` be concrete
von Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach
spaces `M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak
topologies are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star
homomorphism that is ultraweakly continuous. Assume `f` is injective. Let
`B=f.predualPullback : N_* → M_*`, `B(φ)=φ∘f`, and `B*(F)=F∘B`. for every bounded
functional `F ∈ (M_*)*`, `‖B*(F)‖=‖F‖`, with the continuous-dual operator norms. -/
theorem predualPullback_dual_norm (f : NormalStarAlgHom M N) (hf : Function.Injective f)
    (F : StrongDual ℂ (normalFunctionalSpace M)) :
    ‖((ContinuousLinearMap.compL ℂ (normalFunctionalSpace N) (normalFunctionalSpace M) ℂ).flip
      f.predualPullback) F‖ = ‖F‖ := by
  let x : M := (normalFunctionalEvaluationEquiv M).symm F
  have hF : normalFunctionalEvaluationEquiv M x = F :=
    (normalFunctionalEvaluationEquiv M).apply_symm_apply F
  rw [← hF, f.predualPullback_dual_evaluation x]
  rw [(normalFunctionalEvaluationEquiv N).norm_map, (normalFunctionalEvaluationEquiv M).norm_map]
  exact NonUnitalStarAlgHom.norm_map f.toStarAlgHom hf x

/-- **Isometry of the dual precomposition map.** Let `M,N` be concrete von Neumann algebras on
complete complex Hilbert spaces. Their normal-functional Banach spaces `M_*,N_*` are the
norm-closed spans of vector functionals, and their ultraweak topologies are `σ(M,M_*)`,
`σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is ultraweakly
continuous. Assume `f` is injective. Let `B=f.predualPullback : N_* → M_*`, `B(φ)=φ∘f`,
and `B*(F)=F∘B`. `B* : (M_*)* → (N_*)*` is an isometry for the operator-norm metrics. -/
theorem predualPullback_dual_isometry (f : NormalStarAlgHom M N) (hf : Function.Injective f) :
    Isometry ((ContinuousLinearMap.compL ℂ (normalFunctionalSpace N) (normalFunctionalSpace M) ℂ).flip
      f.predualPullback) :=
  AddMonoidHomClass.isometry_of_norm _ (f.predualPullback_dual_norm hf)

end

end VonNeumannAlgebra.NormalStarAlgHom
