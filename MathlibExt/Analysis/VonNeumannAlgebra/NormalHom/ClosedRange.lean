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
# The actual faithful normal operator range is ultraweak closed

The proved original range-annihilator characterization identifies the
actual ultraweak map range with the intersection of zero sets of original
normal-functional evaluations annihilating its predual kernel. Every such
evaluation is actually ultraweak continuous. Their intersection is closed.
No range-closedness, predual quotient or inverse/model certificate is input.
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

/-- The actual original faithful normal-map range is closed in the original target ultraweak topology. -/
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
