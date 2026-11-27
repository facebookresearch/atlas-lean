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
# Doubly stochastic matrices in dimension two

A real doubly stochastic matrix has nonnegative entries and every row and column sum equal to
1. The Birkhoff–von Neumann theorem expresses finite doubly stochastic matrices as convex
combinations of permutation matrices. In size 2, A=[[t,1-t],[1-t,t]] with 0≤t≤1, hence
A=tI+(1-t)P_swap.

Source: G. Birkhoff, Tres observaciones sobre el algebra lineal, Rev. Univ. Nac. Tucumán Ser.
A 5 (1946), 147–151; J. von Neumann (1953); see also D. B. West, Introduction to Graph Theory,
and Bondy–Murty, Graph Theory (2008), for the Hall's-theorem proof.
-/

open Matrix

namespace MathlibExt.LinearAlgebra.Matrix.BirkhoffVonNeumann

/-- **Values of the two-coordinate swap.**

For σ=Equiv.swap 0 1 on Fin 2, σ(0)=1 and σ(1)=0. Its permutation matrix is [[0,1],[1,0]].
-/
private lemma bvn_swap_vals :
    (Equiv.swap (0 : Fin 2) 1) 0 = 1 ∧ (Equiv.swap (0 : Fin 2) 1) 1 = 0 := by
  constructor <;> decide

/-- **Convex-combination classification of a doubly stochastic two-by-two matrix.**

Let A be a real 2×2 matrix with nonnegative entries and row and column sums 1. There exists
t∈[0,1], namely A_(0,0), with A=tI+(1-t)[[0,1],[1,0]].
-/
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
