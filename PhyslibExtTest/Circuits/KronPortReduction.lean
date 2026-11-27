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
    (by ext i; fin_cases i; simp [Matrix.mulVec, dotProduct]; norm_num)
    (by ext i; fin_cases i; simp [Matrix.mulVec, dotProduct]; norm_num)

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
    ⟨by ext i; fin_cases i; simp [Matrix.mulVec, dotProduct]; norm_num,
      by ext i; fin_cases i; simp [Matrix.mulVec, dotProduct]; norm_num⟩).2

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
        (by ext i; fin_cases i; simp [Matrix.mulVec, dotProduct]; norm_num)
        (by ext i; fin_cases i; simp [Matrix.mulVec, dotProduct]; norm_num)
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
    (by ext i; fin_cases i; simp [Matrix.mulVec, dotProduct]; norm_num)

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

/-- Relabeling fixture with two interior nodes swapped:
`A = 3`, `B = [1, 2]`, `D = [[2, 1], [1, 3]]` relabeled by the swap
becomes `B' = [2, 1]`, `D' = [[3, 1], [1, 2]]`, a genuinely different
coupling. -/
example : (!![(2 : ℝ), 1]) ≠ !![1, 2] := by
  intro h
  have := congrFun (congrFun h 0) 0
  norm_num at this

/-- The swapped network has the same Schur complement, through the
public interior reindexing theorem. -/
example : schurComplement !![(3 : ℝ)] !![2, 1] !![3, 1; 1, 2]
    = schurComplement !![(3 : ℝ)] !![1, 2] !![2, 1; 1, 3] := by
  have hB : (!![(1 : ℝ), 2]).submatrix id (Equiv.swap (0 : Fin 2) 1) = !![2, 1] := by
    ext i j; fin_cases i; fin_cases j <;> simp
  have hD : (!![(2 : ℝ), 1; 1, 3]).submatrix (Equiv.swap (0 : Fin 2) 1)
      (Equiv.swap (0 : Fin 2) 1) = !![3, 1; 1, 2] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have h := schurComplement_reindex_interior (Equiv.swap (0 : Fin 2) 1)
    !![(3 : ℝ)] !![1, 2] !![2, 1; 1, 3]
  rwa [hB, hD] at h

/-- The common Schur complement in numbers: `3 - 7 / 5 = 8 / 5`. -/
example : schurComplement !![(3 : ℝ)] !![1, 2] !![2, 1; 1, 3] = !![8 / 5] := by
  ext i j
  fin_cases i; fin_cases j
  simp [schurComplement, Matrix.inv_def, Matrix.adjugate_fin_two, Matrix.det_fin_two_of,
    vecMul, dotProduct, Fin.sum_univ_two, -Matrix.transpose_of]
  norm_num

/-- The swapped network has the same reduced port equation
right-hand side, with interior injection `[1, 0]` relabeled to
`[0, 1]`, through the public interior reindexing theorem. -/
example : ![(1 : ℝ)] - !![(2 : ℝ), 1] *ᵥ ((!![(3 : ℝ), 1; 1, 2])⁻¹ *ᵥ ![0, 1])
    = ![(1 : ℝ)] - !![(1 : ℝ), 2] *ᵥ ((!![(2 : ℝ), 1; 1, 3])⁻¹ *ᵥ ![1, 0]) := by
  have hB : (!![(1 : ℝ), 2]).submatrix id (Equiv.swap (0 : Fin 2) 1) = !![2, 1] := by
    ext i j; fin_cases i; fin_cases j <;> simp
  have hD : (!![(2 : ℝ), 1; 1, 3]).submatrix (Equiv.swap (0 : Fin 2) 1)
      (Equiv.swap (0 : Fin 2) 1) = !![3, 1; 1, 2] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hj : (![(1 : ℝ), 0]) ∘ Equiv.swap (0 : Fin 2) 1 = ![0, 1] := by
    ext i; fin_cases i <;> simp
  have h := (kron_reduction_reindex_interior (Equiv.swap (0 : Fin 2) 1)
    !![(3 : ℝ)] !![1, 2] !![2, 1; 1, 3] ![0] ![1] ![1, 0]).2.1
  rwa [hB, hD, hj] at h

end PhyslibExtTest.Circuits.KronPortReduction
