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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.RangeAnnihilator

/-!
# Ultraweak closedness of an injective normal homomorphism's range

Let `f : M → N` be an injective normal unital complex star homomorphism between concrete von
Neumann algebras. Its range is closed in the ultraweak topology `σ(N,N_*)`.

The range is characterized by vanishing normal-functional evaluations corresponding to the
kernel of the pullback `N_* → M_*`. The conclusion does not assume a normal inverse or prior
closedness of the range.
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

/-- **Ultraweak closed range of an injective normal map.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. Assume `f` is injective. the range of `f.ultraweakMap : Ultraweak
M → Ultraweak N` is closed in the ultraweak topology of `N`. -/
theorem ultraweak_range_isClosed (f : NormalStarAlgHom M N) (hf : Function.Injective f) :
    IsClosed (Set.range f.ultraweakMap) := by
  have hrange : Set.range f.ultraweakMap =
      ⋂ φ : normalFunctionalSpace N, ⋂ _hφ : f.predualPullback φ = 0,
        {y : Ultraweak N | (φ : StrongDual ℂ N) (ultraweakLinearEquiv N y) = 0} := by
    ext y
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, rfl⟩ φ hφ
      rw [f.ultraweakMap_apply, LinearEquiv.apply_symm_apply]
      rw [← f.predualPullback_apply φ (ultraweakLinearEquiv M x), hφ]
      rfl
    · intro hy
      have hmem : ultraweakLinearEquiv N y ∈ Set.range f :=
        (f.mem_range_iff_predual_kernel hf (ultraweakLinearEquiv N y)).mpr hy
      obtain ⟨x, hxy⟩ := hmem
      refine ⟨(ultraweakLinearEquiv M).symm x, ?_⟩
      apply (ultraweakLinearEquiv N).injective
      rw [f.ultraweakMap_apply, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply, hxy]
  rw [hrange]
  apply isClosed_iInter
  intro φ
  apply isClosed_iInter
  intro _hφ
  exact isClosed_eq (ultraweak_eval_continuous N φ) continuous_const

end

end VonNeumannAlgebra.NormalStarAlgHom
