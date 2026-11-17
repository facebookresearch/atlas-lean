/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.SchurSourceEnergy

@[expose] public section

open MathlibExt.LinearAlgebra.Matrix.SchurSourceEnergy Matrix

namespace MathlibExtTest.LinearAlgebra.Matrix.SchurSourceEnergy

/-- The corrected identity holds on the singleton fixture and
the uncorrected one fails there. -/
example :
    (!![(-1 : ℝ)])ᵀ *ᵥ ![1] + !![(2 : ℝ)] *ᵥ ![1] = ![1] ∧
      (![(1 : ℝ)] ⊕ᵥ ![1]) ⬝ᵥ
          (fromBlocks !![(2 : ℝ)] !![-1] (!![(-1 : ℝ)])ᵀ !![2] *ᵥ (![1] ⊕ᵥ ![1])) = 2 ∧
      ![(1 : ℝ)] ⬝ᵥ ((!![(2 : ℝ)] - !![(-1 : ℝ)] * (!![(2 : ℝ)])⁻¹ * (!![(-1 : ℝ)])ᵀ) *ᵥ
          ![1]) = 3 / 2 ∧
      ![(1 : ℝ)] ⬝ᵥ ((!![(2 : ℝ)])⁻¹ *ᵥ ![1]) = 1 / 2 :=
  ⟨singleton_fixture_values.1, singleton_fixture_values.2.1, singleton_fixture_values.2.2.1,
    singleton_fixture_values.2.2.2.1⟩

/-- The generic identity, applied directly to the singleton
fixture: energy `2` splits as Schur `3/2` plus source `1/2`. -/
example :
    (![(1 : ℝ)] ⊕ᵥ ![1]) ⬝ᵥ
        (fromBlocks !![(2 : ℝ)] !![-1] (!![(-1 : ℝ)])ᵀ !![2] *ᵥ (![1] ⊕ᵥ ![1])) =
      ![(1 : ℝ)] ⬝ᵥ ((MathlibExt.LinearAlgebra.Matrix.SchurStrictPositivity.schurComplement !![(2 : ℝ)] !![-1] !![2]) *ᵥ
          ![1]) + ![1] ⬝ᵥ ((!![(2 : ℝ)])⁻¹ *ᵥ ![1]) := by
  haveI : Invertible !![(2 : ℝ)] := by
    haveI : Invertible (!![(2 : ℝ)]).det :=
      ⟨(!![(2 : ℝ)]).det⁻¹, by rw [Matrix.det_fin_one]; norm_num,
        by rw [Matrix.det_fin_one]; norm_num⟩
    exact Matrix.invertibleOfDetInvertible _
  exact dotProduct_fromBlocks_mulVec_eq_schur_add_source_of_interior !![(2 : ℝ)] !![-1] !![2]
    (by
      show (fromBlocks !![(2 : ℝ)] !![-1] (!![(-1 : ℝ)])ᵀ !![2])ᵀ =
        fromBlocks !![(2 : ℝ)] !![-1] (!![(-1 : ℝ)])ᵀ !![2]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.fromBlocks, Matrix.transpose_apply])
    ![1] ![1] ![1] singleton_fixture_values.1

/-- The uncorrected identity fails on the same fixture, via the
generic nonzero-source theorem; the concrete block matrix is
positive definite (its quadratic form is
`2a^2 - 2ab + 2b^2 = a^2 + (a - b)^2 + b^2`). -/
example :
    (![(1 : ℝ)] ⊕ᵥ ![1]) ⬝ᵥ
        (fromBlocks !![(2 : ℝ)] !![-1] (!![(-1 : ℝ)])ᵀ !![2] *ᵥ (![1] ⊕ᵥ ![1])) ≠
      ![(1 : ℝ)] ⬝ᵥ ((MathlibExt.LinearAlgebra.Matrix.SchurStrictPositivity.schurComplement !![(2 : ℝ)] !![-1] !![2]) *ᵥ
          ![1]) := by
  have hG : (fromBlocks !![(2 : ℝ)] !![-1] (!![(-1 : ℝ)])ᵀ !![2]).PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    have hform : ∀ z : Fin 1 ⊕ Fin 1 → ℝ,
        z ⬝ᵥ (fromBlocks !![(2 : ℝ)] !![-1] (!![(-1 : ℝ)])ᵀ !![2] *ᵥ z) =
          2 * (z (Sum.inl 0)) ^ 2 - 2 * (z (Sum.inl 0)) * (z (Sum.inr 0)) +
            2 * (z (Sum.inr 0)) ^ 2 := by
      intro z
      simp only [dotProduct, Matrix.mulVec, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Fintype.sum_sum_type,
        Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.transpose_apply, Matrix.cons_val_fin_one]
      simp
      ring
    refine ⟨by
      ext i j
      rcases i with ⟨i⟩ | ⟨i⟩ <;> rcases j with ⟨j⟩ | ⟨j⟩ <;>
        fin_cases i <;> fin_cases j <;> simp [Matrix.fromBlocks], fun x hx => ?_⟩
    simp only [Pi.star_apply, star_trivial]
    rw [hform]
    have hne : x (Sum.inl 0) ≠ 0 ∨ x (Sum.inr 0) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext fun i => by rcases i with ⟨i⟩ | ⟨i⟩ <;> fin_cases i <;> simp [h.1, h.2])
    rcases hne with h0 | h1
    · nlinarith [sq_nonneg (x (Sum.inl 0) - x (Sum.inr 0)), sq_nonneg (x (Sum.inr 0)),
        sq_pos_of_ne_zero h0]
    · nlinarith [sq_nonneg (x (Sum.inl 0) - x (Sum.inr 0)), sq_nonneg (x (Sum.inl 0)),
        sq_pos_of_ne_zero h1]
  exact dotProduct_fromBlocks_mulVec_ne_schur_of_source_ne_zero !![(2 : ℝ)] !![-1] !![2] hG
    ![1] ![1] (by
      rw [singleton_fixture_values.1]
      simp)

end MathlibExtTest.LinearAlgebra.Matrix.SchurSourceEnergy
