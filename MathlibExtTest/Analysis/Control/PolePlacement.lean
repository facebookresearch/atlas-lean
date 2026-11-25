/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Control.PolePlacement
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

open Polynomial Module MathlibExt.Analysis.Control

namespace MathlibExtTest.Analysis.Control.PolePlacement

/-- The double integrator `ẍ = u` on `ℚ²`, `A = [[0, 1], [0, 0]]`, `b = (0, 1)`: the cyclic
hypothesis holds (`A b = (1, 0)`), so the closed-loop polynomial `(X + 1)²` can be assigned. -/
example : ∃ K : Dual ℚ (Fin 2 → ℚ),
    (Matrix.toLin' !![(0 : ℚ), 1; 0, 0] + K.smulRight ![0, 1]).charpoly = (X + 1) ^ 2 := by
  apply exists_charpoly_add_smulRight_eq
  · rw [eq_top_iff]
    intro x _
    have hx : x = x 0 • (Matrix.toLin' !![(0 : ℚ), 1; 0, 0] ^ ((1 : Fin 2) : ℕ)) ![0, 1] +
        x 1 • (Matrix.toLin' !![(0 : ℚ), 1; 0, 0] ^ ((0 : Fin 2) : ℕ)) ![0, 1] := by
      funext i
      fin_cases i <;> simp
    rw [hx, Module.finrank_fin_fun]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
  · exact (monic_X_add_C 1).pow 2
  · rw [Module.finrank_fin_fun]
    compute_degree!

/-- Several inputs: the fully actuated system `ẋ = u` on `ℚ²` (`A = 0`, `B = id`) can be given
the characteristic polynomial `X² + 1`, which has no rational roots. -/
example : ∃ K : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ),
    ((0 : Module.End ℚ (Fin 2 → ℚ)) + LinearMap.id ∘ₗ K).charpoly = X ^ 2 + 1 := by
  apply exists_charpoly_add_comp_eq
  · rw [eq_top_iff]
    intro x _
    exact Submodule.subset_span ⟨0, by simp, x, by simp⟩
  · exact monic_X_pow_add_C 1 two_ne_zero
  · rw [Module.finrank_fin_fun]
    compute_degree!

end MathlibExtTest.Analysis.Control.PolePlacement
