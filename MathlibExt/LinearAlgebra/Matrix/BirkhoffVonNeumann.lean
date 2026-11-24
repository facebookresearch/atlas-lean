/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @vonbo, Avocado
-/
module

public import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Algebra.BigOperators.Fin
import MathlibExt.LinearAlgebra.Matrix.PermutationEntry

@[expose] public section

/-!
# Birkhoff–von Neumann: permutation-matrix entries and the 2×2 classification

The Birkhoff–von Neumann theorem says every doubly stochastic matrix is a convex combination
of permutation matrices. The general theorem is proved in Mathlib proper
(`Mathlib.Analysis.Convex.Birkhoff`): `doublyStochastic_eq_convexHull_permMatrix`,
`exists_eq_sum_perm_of_mem_doublyStochastic`, and `extremePoints_doublyStochastic`, via the
Kőnig–Hall induction on the number of nonzero entries. This module adds the explicit 2×2
classification, which is convenient for concrete small-matrix computations; the entry
formula for permutation matrices is `Matrix.permMatrix_entry_eq`.

Source: G. Birkhoff, Tres observaciones sobre el algebra lineal, Rev. Univ. Nac. Tucumán
Ser. A 5 (1946), 147–151; J. von Neumann (1953); see also D. B. West, Introduction to Graph
Theory, and Bondy–Murty, Graph Theory (2008), for the Hall's-theorem proof.
-/

open Matrix

namespace MathlibExt.LinearAlgebra.Matrix.BirkhoffVonNeumann

/-- The two permutation matrices of size 2: the identity and the swap. -/
private lemma bvn_swap_vals :
    (Equiv.swap (0 : Fin 2) 1) 0 = 1 ∧ (Equiv.swap (0 : Fin 2) 1) 1 = 0 := by
  constructor <;> decide

/-- Explicit 2×2 classification: every `2 × 2` doubly stochastic matrix is the convex
combination `t • P(1) + (1 - t) • P(swap)` with `t = A 0 0`. -/
public theorem doublyStochastic_fin_two {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A ∈ doublyStochastic ℝ (Fin 2)) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      A = t • (1 : Equiv.Perm (Fin 2)).permMatrix ℝ
        + (1 - t) • (Equiv.swap 0 1).permMatrix ℝ := by
  have hA' := mem_doublyStochastic_iff_sum.mp hA
  obtain ⟨hnn, hrow, hcol⟩ := hA'
  have r0 := hrow 0
  have r1 := hrow 1
  have c0 := hcol 0
  have c1 := hcol 1
  rw [Fin.sum_univ_two] at r0 r1 c0 c1
  obtain ⟨s0, s1⟩ := bvn_swap_vals
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  refine ⟨A 0 0, hnn 0 0, le_one_of_mem_doublyStochastic hA, ?_⟩
  have hP1 : (1 : Equiv.Perm (Fin 2)).permMatrix ℝ = 1 := Matrix.permMatrix_one
  rw [hP1]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    permMatrix_entry_eq]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.mk_zero, Fin.mk_one, s0, s1, h01, h10, ite_true, ite_false,
      mul_one, mul_zero, add_zero, zero_add] <;>
    linarith [r0, r1, c0, c1]

end MathlibExt.LinearAlgebra.Matrix.BirkhoffVonNeumann
