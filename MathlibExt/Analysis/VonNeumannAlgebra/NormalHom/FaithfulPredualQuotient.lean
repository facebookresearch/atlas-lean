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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.FaithfulPredualDual
public import MathlibExt.Analysis.Normed.Operator.DualSurjective

/-!
# Surjective quotient predual pullback for an injective normal map

For an injective normal unital complex star homomorphism `f : M → N`, the bounded pullback `B :
N_* → M_*`, `B(φ)=φ∘f`, is surjective. Every normal functional on `M` is the pullback of one on
`N`.

The topology on `M_*` is the quotient topology induced by `B` from the Banach norm topology on
`N_*`. This is a topological quotient statement; no quotient map or surjectivity is given as a
premise.
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

/-- **Surjective predual pullback of an injective normal map.** Let `M,N` be concrete von
Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. Assume `f` is injective. Let `B=f.predualPullback : N_* → M_*`,
`B(φ)=φ∘f`, and `B*(F)=F∘B`. `B : N_* → M_*` is surjective, so every `ψ ∈ M_*` has `φ ∈
N_*` with `φ∘f=ψ`. -/
theorem predualPullback_surjective_of_injective (f : NormalStarAlgHom M N)
    (hf : Function.Injective f) : Function.Surjective f.predualPullback := by
  apply ContinuousLinearMap.surjective_of_dual_lower_bound
  intro G
  have hnorm := f.predualPullback_dual_norm hf G
  change ‖G.comp f.predualPullback‖ = ‖G‖ at hnorm
  exact hnorm.symm.le

/-- **Banach quotient topology of normal predual pullback.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. Assume `f` is injective. Let `B=f.predualPullback : N_* → M_*`,
`B(φ)=φ∘f`, and `B*(F)=F∘B`. `B : N_* → M_*` is a quotient map for the inherited Banach
norm topologies. -/
theorem predualPullback_isQuotientMap_of_injective (f : NormalStarAlgHom M N)
    (hf : Function.Injective f) : Topology.IsQuotientMap f.predualPullback :=
  f.predualPullback.isQuotientMap (f.predualPullback_surjective_of_injective hf)

end

end VonNeumannAlgebra.NormalStarAlgHom
