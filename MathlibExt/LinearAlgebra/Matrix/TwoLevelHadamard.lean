/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.UnitaryGroup

import MathlibExt.LinearAlgebra.Matrix.FinTwoHadamard
import MathlibExt.LinearAlgebra.Matrix.UnitaryBlockDiagonal
import MathlibExt.Logic.Equiv.TwoPointSumCompl

/-!
# Hadamard action on two chosen coordinates

Put c=1/√2. For indices a,b, the two-level matrix H_(a,b) is the identity away from the a,b
coordinates and has block [[c,c],[c,-c]] there when a≠b. When a=b, it is diagonal with entry c
at a and 1 elsewhere. On a finite index type with a≠b, this is a unitary matrix.
-/

@[expose] public section

namespace Matrix

/-- **Two-level Hadamard matrix.**

Put c=1/√2. For indices a,b, the two-level matrix H_(a,b) is the identity away from the a,b
coordinates and has block [[c,c],[c,-c]] there when a≠b. When a=b, it is diagonal with entry c
at a and 1 elsewhere. The matrix twoLevelHadamard a b is defined on any index type; unitarity
is asserted separately under finiteness and a≠b.
-/
noncomputable def twoLevelHadamard {n : Type*} [DecidableEq n] (a b : n) :
    Matrix n n Complex :=
  fun i j =>
    if i = a then
      if j = a then ((1 : ℝ) / Real.sqrt 2 : Complex)
      else if j = b then ((1 : ℝ) / Real.sqrt 2 : Complex)
      else 0
    else if i = b then
      if j = a then ((1 : ℝ) / Real.sqrt 2 : Complex)
      else if j = b then ((-1 : ℝ) / Real.sqrt 2 : Complex)
      else 0
    else if i = j then 1 else 0

private noncomputable def twoLevelBlock {n : Type*} [DecidableEq n] (a b : n) :
    Matrix (Fin 2 ⊕ {x : n // x ≠ a ∧ x ≠ b})
      (Fin 2 ⊕ {x : n // x ≠ a ∧ x ≠ b}) Complex :=
  Matrix.fromBlocks finTwoHadamard 0 0
    (1 : Matrix {x : n // x ≠ a ∧ x ≠ b} {x : n // x ≠ a ∧ x ≠ b} Complex)

private lemma one_mem_compl {n : Type*} [DecidableEq n] [Fintype n] (a b : n) :
    (1 : Matrix {x : n // x ≠ a ∧ x ≠ b} {x : n // x ≠ a ∧ x ≠ b} Complex) ∈
      Matrix.unitaryGroup _ Complex := by
  rw [Matrix.mem_unitaryGroup_iff]
  simp

private lemma twoLevelBlock_mem {n : Type*} [Fintype n] [DecidableEq n] (a b : n) :
    twoLevelBlock (n := n) a b ∈
      Matrix.unitaryGroup (Fin 2 ⊕ {x : n // x ≠ a ∧ x ≠ b}) Complex := by
  unfold twoLevelBlock
  exact fromBlocks_diagonal_mem_unitaryGroup finTwoHadamard_mem_unitaryGroup
    (one_mem_compl a b)

private theorem reindex_twoLevelBlock_eq {n : Type*} [DecidableEq n] (a b : n)
    (hab : a ≠ b) :
    Matrix.reindex (Equiv.twoPointSumCompl a b hab)
        (Equiv.twoPointSumCompl a b hab) (twoLevelBlock a b) =
      twoLevelHadamard a b := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  unfold twoLevelBlock twoLevelHadamard
  by_cases hia : i = a
  · have hsym_i : (Equiv.twoPointSumCompl a b hab).symm i = Sum.inl 0 := by
      rw [hia, Equiv.twoPointSumCompl_symm_apply_first]
    rw [hsym_i]
    by_cases hja : j = a
    · have hsym_j : (Equiv.twoPointSumCompl a b hab).symm j = Sum.inl 0 := by
        rw [hja, Equiv.twoPointSumCompl_symm_apply_first]
      rw [hsym_j, Matrix.fromBlocks_apply₁₁]
      rw [ite_eq_left hia, ite_eq_left hja]
      simp [finTwoHadamard]
    · by_cases hjb : j = b
      · have hsym_j : (Equiv.twoPointSumCompl a b hab).symm j = Sum.inl 1 := by
          rw [hjb, Equiv.twoPointSumCompl_symm_apply_second]
        rw [hsym_j, Matrix.fromBlocks_apply₁₁]
        rw [ite_eq_left hia, ite_eq_right hja, ite_eq_left hjb]
        simp [finTwoHadamard]
      · have hj1 : j ≠ a := hja
        have hj2 : j ≠ b := hjb
        have hsym_j : (Equiv.twoPointSumCompl a b hab).symm j =
            Sum.inr ⟨j, hj1, hj2⟩ := by
          rw [Equiv.twoPointSumCompl_symm_apply_other _ _ _ _ hj1 hj2]
        rw [hsym_j, Matrix.fromBlocks_apply₁₂]
        rw [ite_eq_left hia, ite_eq_right hja, ite_eq_right hjb]
        simp
  · by_cases hib : i = b
    · have hsym_i : (Equiv.twoPointSumCompl a b hab).symm i = Sum.inl 1 := by
        rw [hib, Equiv.twoPointSumCompl_symm_apply_second]
      rw [hsym_i]
      by_cases hja : j = a
      · have hsym_j : (Equiv.twoPointSumCompl a b hab).symm j = Sum.inl 0 := by
          rw [hja, Equiv.twoPointSumCompl_symm_apply_first]
        rw [hsym_j, Matrix.fromBlocks_apply₁₁]
        rw [ite_eq_right hia, ite_eq_left hib, ite_eq_left hja]
        simp [finTwoHadamard]
      · by_cases hjb : j = b
        · have hsym_j : (Equiv.twoPointSumCompl a b hab).symm j = Sum.inl 1 := by
            rw [hjb, Equiv.twoPointSumCompl_symm_apply_second]
          rw [hsym_j, Matrix.fromBlocks_apply₁₁]
          rw [ite_eq_right hia, ite_eq_left hib, ite_eq_right hja, ite_eq_left hjb]
          simp [finTwoHadamard]
        · have hj1 : j ≠ a := hja
          have hj2 : j ≠ b := hjb
          have hsym_j : (Equiv.twoPointSumCompl a b hab).symm j =
              Sum.inr ⟨j, hj1, hj2⟩ := by
            rw [Equiv.twoPointSumCompl_symm_apply_other _ _ _ _ hj1 hj2]
          rw [hsym_j, Matrix.fromBlocks_apply₁₂]
          rw [ite_eq_right hia, ite_eq_left hib, ite_eq_right hja, ite_eq_right hjb]
          simp
    · have hi1 : i ≠ a := hia
      have hi2 : i ≠ b := hib
      have hsym_i : (Equiv.twoPointSumCompl a b hab).symm i =
          Sum.inr ⟨i, hi1, hi2⟩ := by
        rw [Equiv.twoPointSumCompl_symm_apply_other _ _ _ _ hi1 hi2]
      rw [hsym_i]
      by_cases hja : j = a
      · have hsym_j : (Equiv.twoPointSumCompl a b hab).symm j = Sum.inl 0 := by
          rw [hja, Equiv.twoPointSumCompl_symm_apply_first]
        rw [hsym_j, Matrix.fromBlocks_apply₂₁]
        have hij : i ≠ j := by
          intro hij
          rw [hij, hja] at hia
          exact hia rfl
        rw [ite_eq_right hia, ite_eq_right hib, ite_eq_right hij]
        simp
      · by_cases hjb : j = b
        · have hsym_j : (Equiv.twoPointSumCompl a b hab).symm j = Sum.inl 1 := by
            rw [hjb, Equiv.twoPointSumCompl_symm_apply_second]
          rw [hsym_j, Matrix.fromBlocks_apply₂₁]
          have hij : i ≠ j := by
            intro hij
            rw [hij, hjb] at hib
            exact hib rfl
          rw [ite_eq_right hia, ite_eq_right hib, ite_eq_right hij]
          simp
        · have hj1 : j ≠ a := hja
          have hj2 : j ≠ b := hjb
          have hsym_j : (Equiv.twoPointSumCompl a b hab).symm j =
              Sum.inr ⟨j, hj1, hj2⟩ := by
            rw [Equiv.twoPointSumCompl_symm_apply_other _ _ _ _ hj1 hj2]
          rw [hsym_j, Matrix.fromBlocks_apply₂₂]
          by_cases hij : i = j
          · have heq : (⟨i, hi1, hi2⟩ : {x : n // x ≠ a ∧ x ≠ b}) =
                ⟨j, hj1, hj2⟩ := Subtype.ext hij
            rw [heq]
            rw [ite_eq_right hja, ite_eq_right hjb]
            rw [ite_eq_right hi1, ite_eq_right hi2, ite_eq_left hij]
            simp
          · have hne : (⟨i, hi1, hi2⟩ : {x : n // x ≠ a ∧ x ≠ b}) ≠
                ⟨j, hj1, hj2⟩ := by
              intro h
              exact hij (congrArg Subtype.val h)
            rw [ite_eq_right hja, ite_eq_right hjb]
            rw [ite_eq_right hi1, ite_eq_right hi2, ite_eq_right hij]
            simp [hne]

/-- **Unitarity of the distinct-coordinate Hadamard matrix.**

Put c=1/√2. For indices a,b, the two-level matrix H_(a,b) is the identity away from the a,b
coordinates and has block [[c,c],[c,-c]] there when a≠b. When a=b, it is diagonal with entry c
at a and 1 elsewhere. For a finite index type I and distinct a,b∈I, twoLevelHadamard a b
belongs to U(I,ℂ).
-/
theorem twoLevelHadamard_mem_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n]
    (a b : n) (hab : a ≠ b) :
    twoLevelHadamard a b ∈ Matrix.unitaryGroup n Complex := by
  have hBlock := twoLevelBlock_mem (n := n) a b
  have hRe := reindex_mem_unitaryGroup
    (Equiv.twoPointSumCompl a b hab) hBlock
  have hEq := reindex_twoLevelBlock_eq a b hab
  rw [hEq] at hRe
  exact hRe

/-- **Two-level Hadamard as a unitary element.**

Put c=1/√2. For indices a,b, the two-level matrix H_(a,b) is the identity away from the a,b
coordinates and has block [[c,c],[c,-c]] there when a≠b. When a=b, it is diagonal with entry c
at a and 1 elsewhere. For finite I and a≠b, twoLevelHadamardUnitary a b hab∈U(I,ℂ) has
underlying matrix H_(a,b).
-/
noncomputable def twoLevelHadamardUnitary {n : Type*} [Fintype n] [DecidableEq n]
    (a b : n) (hab : a ≠ b) : Matrix.unitaryGroup n Complex :=
  ⟨twoLevelHadamard a b, twoLevelHadamard_mem_unitaryGroup a b hab⟩

end Matrix
