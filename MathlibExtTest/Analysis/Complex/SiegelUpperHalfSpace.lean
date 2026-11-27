/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.SiegelUpperHalfSpace

open Matrix

namespace Siegel

-- `i` (as a `1 × 1` matrix) lies in `𝔖_1`.
example : !![Complex.I] ∈ upperHalfSpace 1 := by
  rw [mem_upperHalfSpace_one_iff]
  simp

-- `-i` does not.
example : !![-Complex.I] ∉ upperHalfSpace 1 := by
  rw [mem_upperHalfSpace_one_iff]
  simp

-- `J = (0 1; -1 0)` lies in `Sp_{2g}(ℤ)`, for every `g`.
example (g : ℕ) : J g ∈ Sp g := by
  rw [mem_Sp_iff_mem_symplecticGroup, J_eq_neg]
  exact SymplecticGroup.neg_mem (SymplecticGroup.J_mem _ _)

-- The defining equation `ᵗγ J γ = J`, for `γ = J`.
example (g : ℕ) : (J g)ᵀ * J g * J g = J g :=
  (mem_Sp_iff g (J g)).mp (by
    rw [mem_Sp_iff_mem_symplecticGroup, J_eq_neg]
    exact SymplecticGroup.neg_mem (SymplecticGroup.J_mem _ _))

-- Condition S. 3 holds for every `1 × 1` matrix.
example (τ : Matrix (Fin 1) (Fin 1) ℂ) : SiegelS3 τ := siegelS3_of_eq_one τ

-- Condition S. 2 for `i`: the real part is `0`.
example : SiegelS2 !![Complex.I] := by
  intro i j
  fin_cases i; fin_cases j
  norm_num

-- The translation `γ = (1 1; 0 1)` sends `τ` to `τ + 1`.
example (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    smul (fromBlocks (1 : Matrix (Fin g) (Fin g) ℤ) 1 0 1) τ = τ + 1 := by
  simp [smul]

-- A genus-one regression for `smul`, S. 1 and `fundamentalDomain`: `τ = [i/2]` lies in `𝔖_1` and
-- satisfies S. 2 and S. 3, but `γ = J` gives `γ · τ = (-τ)⁻¹ = [2i]`, and S. 1 would need
-- `det Im(γ · τ) = 2 ≤ 1/2 = det Im τ`; so `τ ∉ 𝔉_1`.
example :
    !![Complex.I / 2] ∈ upperHalfSpace 1 ∧ SiegelS2 !![Complex.I / 2] ∧
      SiegelS3 !![Complex.I / 2] ∧ ¬ SiegelS1 !![Complex.I / 2] ∧
      !![Complex.I / 2] ∉ fundamentalDomain 1 := by
  have hJ : J 1 ∈ Sp 1 := by
    rw [mem_Sp_iff_mem_symplecticGroup, J_eq_neg]
    exact SymplecticGroup.neg_mem (SymplecticGroup.J_mem _ _)
  have hsmul : smul (J 1) !![Complex.I / 2] = !![2 * Complex.I] := by
    simp only [smul, J, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
      toBlocks_fromBlocks₂₂, Matrix.map_zero, Matrix.map_one, Int.cast_zero, Int.cast_one, zero_mul,
      zero_add, one_mul, add_zero]
    refine Matrix.inv_eq_right_inv ?_
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply]
    ring_nf
    simp [Complex.I_sq]
  have hS1 : ¬ SiegelS1 !![Complex.I / 2] := by
    intro h
    have := h (J 1) hJ
    rw [hsmul] at this
    simp [Matrix.det_unique] at this
    norm_num at this
  refine ⟨?_, ?_, siegelS3_of_eq_one _, hS1, fun h ↦ hS1 h.2.1⟩
  · rw [mem_upperHalfSpace_one_iff]
    simp
  · intro i j
    fin_cases i; fin_cases j
    simp

end Siegel
