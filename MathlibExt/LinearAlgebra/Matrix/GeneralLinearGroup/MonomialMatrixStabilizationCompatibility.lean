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

public import MathlibExt.GroupTheory.PermutationBilinearTitsStabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Monomial
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.SpecialLinearStabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.MonomialSLStabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.MonomialCoordinateInsertion

/-!
# Stabilization of monomial matrices
-/

@[expose] public section

open Matrix
open Matrix.GeneralLinearGroup
open PermutationBilinearTitsStabilization
open PermutationBilinearCocycle

namespace Matrix.GeneralLinearGroup

/-! ## DeletedIndex vs `Fin.castSucc` -/

theorem deletedIndexLast_insertTuple_eq_tupleSucc
    {n : ℕ} {A : Type*} [Group A] (u : Fin n → A) :
    insertTuple (Fin.last n) (1 : A)
      (fun d : DeletedIndex (Fin (n + 1)) (Fin.last n) =>
        u ((finSuccAboveEquiv (Fin.last n)).symm d)) =
      tupleSucc (n := n) u := by
  ext i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simp [insertTuple_apply_c]
  · simp [insertTuple_apply_of_ne, finSuccAboveEquiv_symm_apply_last,
      tupleSucc_apply_castSucc]

theorem deletedIndexLast_extendPerm_eq_permSuccHom
    {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    extendPerm (Fin.last n)
        (((finSuccAboveEquiv (Fin.last n)).symm.trans σ).trans
          (finSuccAboveEquiv (Fin.last n))) =
      permSuccHom (n := n) σ := by
  ext i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simp [extendPerm_apply_c, permSuccHom_apply_last]
  · simp [extendPerm_apply_of_ne, Equiv.trans_apply,
      finSuccAboveEquiv_apply, Fin.succAbove_last,
      finSuccAboveEquiv_symm_apply_last, permSuccHom_apply_castSucc]

theorem deletedIndexLast_monomialInsert_eq_monomialSuccHom
    {n : ℕ} {A : Type*} [CommGroup A] (x : MonomialBase A (Fin n)) :
    monomialInsert (Fin.last n) (1 : A)
        ⟨fun d => x.left ((finSuccAboveEquiv (Fin.last n)).symm d),
          ((finSuccAboveEquiv (Fin.last n)).symm.trans x.right).trans
            (finSuccAboveEquiv (Fin.last n))⟩ =
      monomialSuccHom (n := n) (A := A) x := by
  apply SemidirectProduct.ext
  · simp only [monomialInsert_left, monomialSuccHom_left]
    exact deletedIndexLast_insertTuple_eq_tupleSucc (n := n) x.left
  · simp only [monomialInsert_right, monomialSuccHom_right]
    exact deletedIndexLast_extendPerm_eq_permSuccHom (n := n) x.right

private theorem monomialMatrixHom_entry
    {R : Type*} [Semiring R] {k : ℕ}
    (x : MonomialBase Rˣ (Fin k)) (i j : Fin k) :
    (↑(monomialMatrixHom R (Fin k) x) :
        Matrix (Fin k) (Fin k) R) i j =
      if (x.right⁻¹ i = j) then (x.left i : R) else 0 := by
  have h_eq :
      (↑(monomialMatrixHom R (Fin k) x) :
        Matrix (Fin k) (Fin k) R) =
        Matrix.diagonal (fun t => (x.left t : R)) *
          (x.right⁻¹).permMatrix R := by
    cases x with
    | mk u σ =>
      rfl
  rw [h_eq]
  simp [Matrix.diagonal_mul, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

/-! ## Main GL bridge -/

theorem monomialMatrixHom_monomialSuccHom
    {R : Type*} [CommSemiring R] {n : ℕ}
    (x : MonomialBase Rˣ (Fin n)) :
    monomialMatrixHom R (Fin (n + 1))
        (monomialSuccHom (n := n) x) =
      Matrix.GeneralLinearGroup.stabilization R
        (monomialMatrixHom R (Fin n) x) := by
  apply Units.ext
  ext i j
  have hL :
      (↑(monomialMatrixHom R (Fin (n + 1))
            (monomialSuccHom (n := n) x)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j =
        if ((monomialSuccHom (n := n) x).right⁻¹ i = j)
          then (((monomialSuccHom (n := n) x).left i : Rˣ) : R)
          else 0 :=
    monomialMatrixHom_entry (monomialSuccHom (n := n) x) i j
  have hR :
      (↑(Matrix.GeneralLinearGroup.stabilization R
            (monomialMatrixHom R (Fin n) x)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j =
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks
            (↑(monomialMatrixHom R (Fin n) x) :
              Matrix (Fin n) (Fin n) R) 0 0 1) i j := by
    simp [Matrix.GeneralLinearGroup.coe_stabilization]
  rw [hL, hR]
  have h_perm_right :
      (monomialSuccHom (n := n) (A := Rˣ) x).right =
        permSuccHom (n := n) x.right := rfl
  have h_tuple_left :
      (monomialSuccHom (n := n) (A := Rˣ) x).left =
        tupleSuccHom (n := n) x.left := rfl
  have h_inv :
      (monomialSuccHom (n := n) (A := Rˣ) x).right⁻¹ =
        permSuccHom (n := n) x.right⁻¹ := by
    rw [h_perm_right, permSuccHom_inv]
  refine Fin.lastCases ?_ (fun a => ?_) i
  · refine Fin.lastCases ?_ (fun b => ?_) j
    · -- i = last, j = last
      have h_last_inv : (monomialSuccHom (n := n) x).right⁻¹ (Fin.last n) =
          Fin.last n := by
        rw [h_inv, permSuccHom_apply_last]
      have h_last_tuple :
          ((monomialSuccHom (n := n) x).left (Fin.last n) : R) = 1 := by
        simp only [h_tuple_left, tupleSuccHom_apply_last]
        rfl
      have h_reindex_last :
          Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks
                (↑(monomialMatrixHom R (Fin n) x) :
                  Matrix (Fin n) (Fin n) R) 0 0 1)
              (Fin.last n) (Fin.last n) = 1 := by
        simp [Matrix.reindex_apply, finSumFinEquiv_symm_last,
          Matrix.fromBlocks_apply₂₂]
      rw [h_reindex_last]
      simp only [h_last_inv, h_last_tuple, ite_true]
    · -- i = last, j = castSucc b
      have h_ne : (permSuccHom (n := n) x.right)⁻¹ (Fin.last n) ≠
          Fin.castSucc b := by
        simp only [permSuccHom_inv, permSuccHom_apply_last]
        exact Ne.symm (ne_of_lt (Fin.castSucc_lt_last b))
      have h_ne' : (monomialSuccHom (n := n) x).right⁻¹ (Fin.last n) ≠
          Fin.castSucc b := by
        rw [h_inv]
        exact h_ne
      have h_reindex :
          Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks
                (↑(monomialMatrixHom R (Fin n) x) :
                  Matrix (Fin n) (Fin n) R) 0 0 1)
              (Fin.last n) (Fin.castSucc b) = 0 := by
        simp [Matrix.reindex_apply, finSumFinEquiv_symm_last,
          finSumFinEquiv_symm_apply_castSucc, Matrix.fromBlocks_apply₂₁]
      rw [h_reindex, ite_eq_right h_ne']
  · -- i = castSucc a
    refine Fin.lastCases ?_ (fun b => ?_) j
    · have h_ne :
          (permSuccHom (n := n) x.right)⁻¹ (Fin.castSucc a) ≠
            Fin.last n := by
        rw [permSuccHom_inv, permSuccHom_apply_castSucc]
        exact ne_of_lt (Fin.castSucc_lt_last _)
      have h_ne' : (monomialSuccHom (n := n) x).right⁻¹ (Fin.castSucc a) ≠
          Fin.last n := by
        rw [h_inv]
        exact h_ne
      have h_reindex :
          Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks
                (↑(monomialMatrixHom R (Fin n) x) :
                  Matrix (Fin n) (Fin n) R) 0 0 1)
              (Fin.castSucc a) (Fin.last n) = 0 := by
        simp [Matrix.reindex_apply, finSumFinEquiv_symm_apply_castSucc,
          finSumFinEquiv_symm_last, Matrix.fromBlocks_apply₁₂]
      rw [h_reindex, ite_eq_right h_ne']
    · -- i = castSucc a, j = castSucc b
      have h_perm : ((permSuccHom (n := n) x.right)⁻¹
            (Fin.castSucc a) = Fin.castSucc b) ↔
          (x.right⁻¹ a = b) := by
        simp only [permSuccHom_inv, permSuccHom_apply_castSucc,
          Fin.castSucc_inj]
      have h_perm' : ((monomialSuccHom (n := n) x).right⁻¹
            (Fin.castSucc a) = Fin.castSucc b) ↔
          (x.right⁻¹ a = b) := by
        rw [h_inv]
        exact h_perm
      have h_reindex : Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks
              (↑(monomialMatrixHom R (Fin n) x) :
                Matrix (Fin n) (Fin n) R) 0 0 1)
            (Fin.castSucc a) (Fin.castSucc b) =
          (↑(monomialMatrixHom R (Fin n) x) :
            Matrix (Fin n) (Fin n) R) a b := by
        simp [Matrix.reindex_apply, finSumFinEquiv_symm_apply_castSucc,
          Matrix.fromBlocks_apply₁₁]
      have h_entry : (↑(monomialMatrixHom R (Fin n) x) :
            Matrix (Fin n) (Fin n) R) a b =
          if (x.right⁻¹ a = b) then (x.left a : R) else 0 :=
        monomialMatrixHom_entry x a b
      have h_tuple : ((monomialSuccHom (n := n) x).left
          (Fin.castSucc a) : R) = (x.left a : R) := by
        simp only [h_tuple_left, tupleSuccHom_apply_castSucc]
      rw [h_reindex, h_entry]
      by_cases h_eq : x.right⁻¹ a = b
      · simp only [h_perm', h_eq, h_tuple, ite_true]
      · simp only [h_perm', h_eq, h_tuple, ite_false]

/-! ## Main SL bridge -/

theorem monomialSLHom_monomialSLSuccHom
    {R : Type*} [CommRing R] {n : ℕ}
    (m : MonomialSL R (Fin n)) :
    monomialSLHom R (Fin (n + 1))
        (monomialSLSuccHom (R := R) m) =
      Matrix.SpecialLinearGroup.stabilization R
        (monomialSLHom R (Fin n) m) := by
  apply Subtype.ext
  have hGL :
      (↑(monomialSLHom R (Fin (n + 1))
            (monomialSLSuccHom (R := R) m) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) R)) =
        (↑(monomialMatrixHom R (Fin (n + 1))
            (monomialSuccHom (n := n) (m : MonomialBase Rˣ (Fin n))) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) R)) := by
    simp only [coe_monomialSLHom, coe_monomialSLSuccHom]
  have hGL2 :
      (↑(Matrix.SpecialLinearGroup.stabilization R
            (monomialSLHom R (Fin n) m) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) R)) =
        (↑(Matrix.GeneralLinearGroup.stabilization R
            (monomialMatrixHom R (Fin n)
              (m : MonomialBase Rˣ (Fin n))) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) R)) := by
    simp only [Matrix.SpecialLinearGroup.coe_stabilization,
      monomialSLHom_toGL]
  rw [hGL, hGL2]
  exact congrArg Units.val
    (monomialMatrixHom_monomialSuccHom
      (R := R) (x := (m : MonomialBase Rˣ (Fin n))))

end Matrix.GeneralLinearGroup
