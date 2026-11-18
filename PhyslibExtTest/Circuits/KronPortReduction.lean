/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.KronPortReduction
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

@[expose] public section

open Matrix PhyslibExt.Circuits.KronPortReduction
open MathlibExt.LinearAlgebra.Matrix.SchurStrictPositivity
open MathlibExt.LinearAlgebra.Matrix.SchurSourceEnergy

namespace PhyslibExtTest.Circuits.KronPortReduction

/-- The scalar fixture in numbers: total dissipation `14 / 3` splits
as reduced port dissipation `25 / 6` plus source term `1 / 2`. -/
example : (14 : ℝ) / 3 = 25 / 6 + 1 / 2 := by norm_num

/-- Reduced port injection on the scalar fixture
`A = 2`, `B = 1`, `D = 2`, `φP = 5 / 3`, `φI = -1 / 3`,
`jP = 3`, `jI = 1`, through the public reduced-injection lemma. -/
example : schurComplement !![(2 : ℝ)] !![1] !![2] *ᵥ ![(5 / 3 : ℝ)]
    = ![3] - !![1] *ᵥ ((!![(2 : ℝ)])⁻¹ *ᵥ ![1]) := by
  letI : Invertible !![(2 : ℝ)] := by
    letI : Invertible (!![(2 : ℝ)]).det :=
      ⟨(!![(2 : ℝ)]).det⁻¹, by rw [Matrix.det_fin_one]; norm_num,
        by rw [Matrix.det_fin_one]; norm_num⟩
    exact Matrix.invertibleOfDetInvertible _
  exact reduced_injection_of_full_solution !![(2 : ℝ)] !![1] !![2]
    ![(5 / 3 : ℝ)] ![(-1 / 3 : ℝ)] ![3] ![1]
    (by ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct] <;> norm_num)
    (by ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct] <;> norm_num)

/-- Interior reconstruction on the scalar fixture: the interior
potential `-1 / 3` is recovered from the port potential, through
the public block equivalence. -/
example : ![(-1 / 3 : ℝ)]
    = (!![(2 : ℝ)])⁻¹ *ᵥ (![1] - (!![(1 : ℝ)])ᵀ *ᵥ ![(5 / 3 : ℝ)]) := by
  letI : Invertible !![(2 : ℝ)] := by
    letI : Invertible (!![(2 : ℝ)]).det :=
      ⟨(!![(2 : ℝ)]).det⁻¹, by rw [Matrix.det_fin_one]; norm_num,
        by rw [Matrix.det_fin_one]; norm_num⟩
    exact Matrix.invertibleOfDetInvertible _
  exact ((block_solution_iff_reduced !![(2 : ℝ)] !![1] !![2]
    ![(5 / 3 : ℝ)] ![(-1 / 3 : ℝ)] ![3] ![1]).mp
    ⟨by ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct] <;> norm_num,
      by ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct] <;> norm_num⟩).2

/-- Reconstruction from the reduced solution on the scalar fixture
solves the full system, through the public reconstruction lemma. -/
example : !![(2 : ℝ)] *ᵥ ![(5 / 3 : ℝ)]
      + !![1] *ᵥ ((!![(2 : ℝ)])⁻¹ *ᵥ (![1] - (!![(1 : ℝ)])ᵀ *ᵥ ![(5 / 3 : ℝ)]))
      = ![3]
    ∧ (!![(1 : ℝ)])ᵀ *ᵥ ![(5 / 3 : ℝ)]
      + !![2] *ᵥ ((!![(2 : ℝ)])⁻¹ *ᵥ (![1] - (!![(1 : ℝ)])ᵀ *ᵥ ![(5 / 3 : ℝ)]))
      = ![1] := by
  letI : Invertible !![(2 : ℝ)] := by
    letI : Invertible (!![(2 : ℝ)]).det :=
      ⟨(!![(2 : ℝ)]).det⁻¹, by rw [Matrix.det_fin_one]; norm_num,
        by rw [Matrix.det_fin_one]; norm_num⟩
    exact Matrix.invertibleOfDetInvertible _
  exact full_solution_of_reduced !![(2 : ℝ)] !![1] !![2] ![(5 / 3 : ℝ)] ![3] ![1]
    (by
      have h := reduced_injection_of_full_solution !![(2 : ℝ)] !![1] !![2]
        ![(5 / 3 : ℝ)] ![(-1 / 3 : ℝ)] ![3] ![1]
        (by ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct] <;> norm_num)
        (by ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct] <;> norm_num)
      exact h)

/-- Dissipation split on the scalar fixture, through the canonical
Schur source energy identity: total dissipation is the reduced
port dissipation plus the retained source term. -/
example : (![(5 / 3 : ℝ)] ⊕ᵥ ![(-1 / 3 : ℝ)]) ⬝ᵥ
      (fromBlocks !![(2 : ℝ)] !![1] (!![(1 : ℝ)])ᵀ !![2] *ᵥ
        (![(5 / 3 : ℝ)] ⊕ᵥ ![(-1 / 3 : ℝ)]))
    = ![(5 / 3 : ℝ)] ⬝ᵥ (schurComplement !![(2 : ℝ)] !![1] !![2] *ᵥ ![(5 / 3 : ℝ)])
      + ![1] ⬝ᵥ ((!![(2 : ℝ)])⁻¹ *ᵥ ![1]) := by
  letI : Invertible !![(2 : ℝ)] := by
    letI : Invertible (!![(2 : ℝ)]).det :=
      ⟨(!![(2 : ℝ)]).det⁻¹, by rw [Matrix.det_fin_one]; norm_num,
        by rw [Matrix.det_fin_one]; norm_num⟩
    exact Matrix.invertibleOfDetInvertible _
  exact dotProduct_fromBlocks_mulVec_eq_schur_add_source_of_interior !![(2 : ℝ)] !![1] !![2]
    (by
      show (fromBlocks !![(2 : ℝ)] !![1] (!![(1 : ℝ)])ᵀ !![2])ᵀ
        = fromBlocks !![(2 : ℝ)] !![1] (!![(1 : ℝ)])ᵀ !![2]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.fromBlocks, Matrix.transpose_apply])
    ![(5 / 3 : ℝ)] ![(-1 / 3 : ℝ)] ![1]
    (by ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct] <;> norm_num)

/-- The same split evaluated in numbers: the total is `14 / 3`. -/
example : (![(5 / 3 : ℝ)] ⊕ᵥ ![(-1 / 3 : ℝ)]) ⬝ᵥ
      (fromBlocks !![(2 : ℝ)] !![1] (!![(1 : ℝ)])ᵀ !![2] *ᵥ
        (![(5 / 3 : ℝ)] ⊕ᵥ ![(-1 / 3 : ℝ)]))
    = (14 : ℝ) / 3 := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_one,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.transpose_apply, Matrix.cons_val_fin_one, Sum.elim_inl,
    Sum.elim_inr]
  norm_num

/-- Source-free dissipation on the scalar fixture with zero interior
injection, through the canonical source-free identity. -/
example : (![(5 / 3 : ℝ)] ⊕ᵥ ![(-5 / 6 : ℝ)]) ⬝ᵥ
      (fromBlocks !![(2 : ℝ)] !![1] (!![(1 : ℝ)])ᵀ !![2] *ᵥ
        (![(5 / 3 : ℝ)] ⊕ᵥ ![(-5 / 6 : ℝ)]))
    = ![(5 / 3 : ℝ)] ⬝ᵥ (schurComplement !![(2 : ℝ)] !![1] !![2] *ᵥ ![(5 / 3 : ℝ)]) := by
  letI : Invertible !![(2 : ℝ)] := by
    letI : Invertible (!![(2 : ℝ)]).det :=
      ⟨(!![(2 : ℝ)]).det⁻¹, by rw [Matrix.det_fin_one]; norm_num,
        by rw [Matrix.det_fin_one]; norm_num⟩
    exact Matrix.invertibleOfDetInvertible _
  exact dotProduct_fromBlocks_mulVec_eq_schur_of_interior_zero !![(2 : ℝ)] !![1] !![2]
    (by
      show (fromBlocks !![(2 : ℝ)] !![1] (!![(1 : ℝ)])ᵀ !![2])ᵀ
        = fromBlocks !![(2 : ℝ)] !![1] (!![(1 : ℝ)])ᵀ !![2]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.fromBlocks, Matrix.transpose_apply])
    ![(5 / 3 : ℝ)] ![(-5 / 6 : ℝ)]
    (by ext i; fin_cases i; simp [Matrix.mulVec, dotProduct]; norm_num)

end PhyslibExtTest.Circuits.KronPortReduction
