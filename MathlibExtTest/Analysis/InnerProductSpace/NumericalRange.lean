/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Leonard Dinh
-/
module

public import MathlibExt.Analysis.InnerProductSpace.NumericalRange

@[expose] public section

namespace MathlibExtTest.Analysis.InnerProductSpace.NumericalRange

open MetaMathlibExt

-- Analysis 382: Numerical Range

theorem numericalRange_identity_two :
    numericalRange !![(1 : ℂ), 0; 0, 1] = {1} := by
  rw [← Matrix.one_fin_two]
  ext z
  simp only [numericalRange, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hId :
        (1 : Matrix (Fin 2) (Fin 2) ℂ).toEuclideanLin =
          LinearMap.id :=
      Matrix.toLpLin_one 2
    rw [hId, LinearMap.id_apply, inner_self_eq_norm_sq_to_K, hx]
    norm_num
  · intro hz
    subst hz
    refine ⟨PiLp.single 2 (0 : Fin 2) (1 : ℂ), ?_, ?_⟩
    · rw [PiLp.norm_single]
      norm_num
    · have hId :
          (1 : Matrix (Fin 2) (Fin 2) ℂ).toEuclideanLin =
            LinearMap.id :=
        Matrix.toLpLin_one 2
      rw [hId, LinearMap.id_apply, inner_self_eq_norm_sq_to_K]
      rw [PiLp.norm_single]
      norm_num

end MathlibExtTest.Analysis.InnerProductSpace.NumericalRange

end
