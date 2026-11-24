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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergRootSubgroups
public import MathlibExt.KTheory.Ring.K2.StableSteinbergToElementary
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BlockUnipotent
import MathlibExt.KTheory.Ring.StableElementary.Inclusions
import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.WeakBlockLDU

/-! # Stable Steinberg root injectivity

`toStableE` is injective on the last-column and last-row root subgroups.

Finite `n+1` block-evaluation API: `lastBoundaryBlockElementary` and its
coercion and `toStableE` evaluation lemmas, including transparent
`List.prod` transport and the `fromFinite`-injective descent of a stable
trivial word to its finite elementary representative.
-/

namespace AlgebraicKTheory
namespace StableSteinberg

open Matrix
open Matrix.GeneralLinearGroup

universe u

variable {R : Type u} [Ring R]

private def colMatrix (n : ℕ) (v : Fin n → Multiplicative R) :
    Matrix (Fin n) (Fin 1) R :=
  Matrix.of fun i _ => (v i).toAdd

private def rowMatrix (n : ℕ) (v : Fin n → Multiplicative R) :
    Matrix (Fin 1) (Fin n) R :=
  Matrix.of fun _ j => (v j).toAdd

private def colEquiv (n : ℕ) : Fin n ⊕ Fin 1 ≃ Fin (n + 1) :=
  finSumFinEquiv (m := n) (n := 1)

private def colGL (n : ℕ) (v : Fin n → Multiplicative R) :
    Matrix.GeneralLinearGroup (Fin (n + 1)) R :=
  reindexMulEquiv (colEquiv n)
    (BlockElementary.upperUnit (colMatrix n v))

private def rowGL (n : ℕ) (v : Fin n → Multiplicative R) :
    Matrix.GeneralLinearGroup (Fin (n + 1)) R :=
  reindexMulEquiv (colEquiv n)
    (BlockElementary.lowerUnit (rowMatrix n v))

private lemma colMatrix_zero (n : ℕ) :
    colMatrix n (1 : Fin n → Multiplicative R) = 0 := by
  ext i j
  simp [colMatrix]

private lemma rowMatrix_zero (n : ℕ) :
    rowMatrix n (1 : Fin n → Multiplicative R) = 0 := by
  ext i j
  simp [rowMatrix]

private lemma colMatrix_add (n : ℕ) (v w : Fin n → Multiplicative R) :
    colMatrix n (v * w) = colMatrix n v + colMatrix n w := by
  ext i j
  simp [colMatrix, Matrix.of_apply]

private lemma rowMatrix_add (n : ℕ) (v w : Fin n → Multiplicative R) :
    rowMatrix n (v * w) = rowMatrix n v + rowMatrix n w := by
  ext i j
  simp [rowMatrix, Matrix.of_apply]

private lemma colMatrix_single (n : ℕ) (i : Fin n)
    (a : Multiplicative R) :
    colMatrix n (Pi.mulSingle i a) =
      Matrix.single i (0 : Fin 1) a.toAdd := by
  ext x y
  have hy : y = 0 := Subsingleton.elim y 0
  subst hy
  by_cases hx : x = i
  · simp [hx, colMatrix, Matrix.of_apply]
  · simp [hx, Ne.symm hx, colMatrix, Matrix.of_apply]

private lemma rowMatrix_single (n : ℕ) (i : Fin n)
    (a : Multiplicative R) :
    rowMatrix n (Pi.mulSingle i a) =
      Matrix.single (0 : Fin 1) i a.toAdd := by
  ext x y
  have hx : x = 0 := Subsingleton.elim x 0
  subst hx
  by_cases hy : y = i
  · simp [hy, rowMatrix, Matrix.of_apply]
  · simp [hy, Ne.symm hy, rowMatrix, Matrix.of_apply]

private noncomputable def colHom (n : ℕ) :
    (Fin n → Multiplicative R) →* Matrix.GeneralLinearGroup (Fin (n + 1)) R where
  toFun := colGL n
  map_one' := by
    simp [colGL, colMatrix_zero, BlockElementary.upperUnit_zero]
  map_mul' := by
    intro v w
    have hAdd : colMatrix n (v * w) = colMatrix n v + colMatrix n w :=
      colMatrix_add n v w
    calc colGL n (v * w)
        = reindexMulEquiv (colEquiv n)
            (BlockElementary.upperUnit (colMatrix n (v * w))) := rfl
      _ = reindexMulEquiv (colEquiv n)
            (BlockElementary.upperUnit (colMatrix n v + colMatrix n w)) := by
          rw [hAdd]
      _ = reindexMulEquiv (colEquiv n)
            (BlockElementary.upperUnit (colMatrix n v) *
              BlockElementary.upperUnit (colMatrix n w)) := by
          rw [BlockElementary.upperUnit_add]
      _ = reindexMulEquiv (colEquiv n)
              (BlockElementary.upperUnit (colMatrix n v)) *
            reindexMulEquiv (colEquiv n)
              (BlockElementary.upperUnit (colMatrix n w)) := by
          rw [MulEquiv.map_mul]

private noncomputable def rowHom (n : ℕ) :
    (Fin n → Multiplicative R) →* Matrix.GeneralLinearGroup (Fin (n + 1)) R where
  toFun := rowGL n
  map_one' := by
    simp [rowGL, rowMatrix_zero, BlockElementary.lowerUnit_zero]
  map_mul' := by
    intro v w
    have hAdd : rowMatrix n (v * w) = rowMatrix n v + rowMatrix n w :=
      rowMatrix_add n v w
    calc rowGL n (v * w)
        = reindexMulEquiv (colEquiv n)
            (BlockElementary.lowerUnit (rowMatrix n (v * w))) := rfl
      _ = reindexMulEquiv (colEquiv n)
            (BlockElementary.lowerUnit (rowMatrix n v + rowMatrix n w)) := by
          rw [hAdd]
      _ = reindexMulEquiv (colEquiv n)
            (BlockElementary.lowerUnit (rowMatrix n v) *
              BlockElementary.lowerUnit (rowMatrix n w)) := by
          rw [BlockElementary.lowerUnit_add]
      _ = reindexMulEquiv (colEquiv n)
              (BlockElementary.lowerUnit (rowMatrix n v)) *
            reindexMulEquiv (colEquiv n)
              (BlockElementary.lowerUnit (rowMatrix n w)) := by
          rw [MulEquiv.map_mul]

private lemma colHom_injective (n : ℕ) :
    Function.Injective (colHom (R := R) n) := by
  intro v w h
  have h_eq : colGL n v = colGL n w := h
  have h_reindex :
      BlockElementary.upperUnit (colMatrix n v) =
        BlockElementary.upperUnit (colMatrix n w) :=
    (MulEquiv.injective (reindexMulEquiv (colEquiv n))) h_eq
  have h_val :
      (↑(BlockElementary.upperUnit (colMatrix n v)) :
        Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R) =
      (↑(BlockElementary.upperUnit (colMatrix n w)) : Matrix _ _ R) :=
    congrArg Units.val h_reindex
  simp only [BlockElementary.coe_upperUnit] at h_val
  have h_mat : colMatrix n v = colMatrix n w := by
    ext i j
    have h_ij :=
      congrFun (congrFun h_val (Sum.inl i)) (Sum.inr j)
    simp only [Matrix.fromBlocks_apply₁₂] at h_ij
    simpa [colMatrix, Matrix.of_apply] using h_ij
  funext i
  have h_i := congrFun (congrFun h_mat i) (0 : Fin 1)
  simp only [colMatrix, Matrix.of_apply] at h_i
  have : v i = w i := by
    have hv : Multiplicative.ofAdd (v i).toAdd = v i := rfl
    have hw : Multiplicative.ofAdd (w i).toAdd = w i := rfl
    rw [← hv, ← hw, h_i]
  exact this

private lemma rowHom_injective (n : ℕ) :
    Function.Injective (rowHom (R := R) n) := by
  intro v w h
  have h_eq : rowGL n v = rowGL n w := h
  have h_reindex :
      BlockElementary.lowerUnit (rowMatrix n v) =
        BlockElementary.lowerUnit (rowMatrix n w) :=
    (MulEquiv.injective (reindexMulEquiv (colEquiv n))) h_eq
  have h_val :
      (↑(BlockElementary.lowerUnit (rowMatrix n v)) :
        Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R) =
      (↑(BlockElementary.lowerUnit (rowMatrix n w)) : Matrix _ _ R) :=
    congrArg Units.val h_reindex
  simp only [BlockElementary.coe_lowerUnit] at h_val
  have h_mat : rowMatrix n v = rowMatrix n w := by
    ext i j
    have h_ij :=
      congrFun (congrFun h_val (Sum.inr i)) (Sum.inl j)
    simp only [Matrix.fromBlocks_apply₂₁] at h_ij
    simpa [rowMatrix, Matrix.of_apply] using h_ij
  funext i
  have h_i := congrFun (congrFun h_mat (0 : Fin 1)) i
  simp only [rowMatrix, Matrix.of_apply] at h_i
  have : v i = w i := by
    have hv : Multiplicative.ofAdd (v i).toAdd = v i := rfl
    have hw : Multiplicative.ofAdd (w i).toAdd = w i := rfl
    rw [← hv, ← hw, h_i]
  exact this

private lemma colHij_neq (n : ℕ) (i : Fin n) :
    colEquiv n (Sum.inl i) ≠ colEquiv n (Sum.inr (0 : Fin 1)) := by
  intro h
  have h_inj := (colEquiv n).injective h
  cases h_inj

private lemma rowHij_neq (n : ℕ) (i : Fin n) :
    colEquiv n (Sum.inr (0 : Fin 1)) ≠ colEquiv n (Sum.inl i) := by
  intro h
  have h_inj := (colEquiv n).injective h
  cases h_inj

private lemma colHom_single (n : ℕ) (i : Fin n)
    (a : Multiplicative R) :
    colHom n (Pi.mulSingle i a) =
      Matrix.GeneralLinearGroup.elementary
        (colEquiv n (Sum.inl i))
        (colEquiv n (Sum.inr (0 : Fin 1)))
        (colHij_neq n i) a.toAdd := by
  have h_col :
      colMatrix n (Pi.mulSingle i a) =
        Matrix.single i (0 : Fin 1) a.toAdd :=
    colMatrix_single n i a
  calc colHom n (Pi.mulSingle i a)
      = reindexMulEquiv (colEquiv n)
          (BlockElementary.upperUnit (colMatrix n (Pi.mulSingle i a))) := rfl
    _ = reindexMulEquiv (colEquiv n)
          (BlockElementary.upperUnit (Matrix.single i 0 a.toAdd)) := by
        rw [h_col]
    _ = reindexMulEquiv (colEquiv n)
          (Matrix.GeneralLinearGroup.elementary
            (Sum.inl i) (Sum.inr (0 : Fin 1)) Sum.inl_ne_inr a.toAdd) := by
        rw [BlockElementary.upperUnit_single]
    _ = Matrix.GeneralLinearGroup.elementary
          (colEquiv n (Sum.inl i))
          (colEquiv n (Sum.inr (0 : Fin 1)))
          (colHij_neq n i) a.toAdd := by
        rw [Matrix.GeneralLinearGroup.reindexMulEquiv_elementary]

private lemma rowHom_single (n : ℕ) (i : Fin n)
    (a : Multiplicative R) :
    rowHom n (Pi.mulSingle i a) =
      Matrix.GeneralLinearGroup.elementary
        (colEquiv n (Sum.inr (0 : Fin 1)))
        (colEquiv n (Sum.inl i))
        (rowHij_neq n i) a.toAdd := by
  have h_row :
      rowMatrix n (Pi.mulSingle i a) =
        Matrix.single (0 : Fin 1) i a.toAdd :=
    rowMatrix_single n i a
  calc rowHom n (Pi.mulSingle i a)
      = reindexMulEquiv (colEquiv n)
          (BlockElementary.lowerUnit (rowMatrix n (Pi.mulSingle i a))) := rfl
    _ = reindexMulEquiv (colEquiv n)
          (BlockElementary.lowerUnit (Matrix.single 0 i a.toAdd)) := by
        rw [h_row]
    _ = reindexMulEquiv (colEquiv n)
          (Matrix.GeneralLinearGroup.elementary
            (Sum.inr (0 : Fin 1)) (Sum.inl i) Sum.inr_ne_inl a.toAdd) := by
        rw [BlockElementary.lowerUnit_single]
    _ = Matrix.GeneralLinearGroup.elementary
          (colEquiv n (Sum.inr (0 : Fin 1)))
          (colEquiv n (Sum.inl i))
          (rowHij_neq n i) a.toAdd := by
        rw [Matrix.GeneralLinearGroup.reindexMulEquiv_elementary]

private lemma colHom_mem (n : ℕ) (v : Fin n → Multiplicative R) :
    colHom n v ∈
      Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) R := by
  have h_mem :
      BlockElementary.upperUnit (colMatrix n v) ∈
        Matrix.GeneralLinearGroup.elementarySubgroup (Fin n ⊕ Fin 1) R :=
    BlockElementary.upperUnit_mem_elementarySubgroup _
  exact Matrix.GeneralLinearGroup.reindexMulEquiv_mem_elementarySubgroup (colEquiv n) h_mem

private lemma rowHom_mem (n : ℕ) (v : Fin n → Multiplicative R) :
    rowHom n v ∈
      Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) R := by
  have h_mem :
      BlockElementary.lowerUnit (rowMatrix n v) ∈
        Matrix.GeneralLinearGroup.elementarySubgroup (Fin n ⊕ Fin 1) R :=
    BlockElementary.lowerUnit_mem_elementarySubgroup _
  exact Matrix.GeneralLinearGroup.reindexMulEquiv_mem_elementarySubgroup (colEquiv n) h_mem

private noncomputable def colSubgroupHom (n : ℕ) :
    (Fin n → Multiplicative R) →*
      ↥(Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) R) :=
  (colHom n).codRestrict _ (colHom_mem n)

private noncomputable def rowSubgroupHom (n : ℕ) :
    (Fin n → Multiplicative R) →*
      ↥(Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) R) :=
  (rowHom n).codRestrict _ (rowHom_mem n)

private noncomputable def colStableHom (n : ℕ) :
    (Fin n → Multiplicative R) →* AlgebraicKTheory.StableE R :=
  (AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)).comp
    (colSubgroupHom n)

private noncomputable def rowStableHom (n : ℕ) :
    (Fin n → Multiplicative R) →* AlgebraicKTheory.StableE R :=
  (AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)).comp
    (rowSubgroupHom n)

private lemma colSubgroupHom_injective (n : ℕ) :
    Function.Injective (colSubgroupHom (R := R) n) := by
  intro v w h
  have h_val :
      (colHom n v : Matrix.GeneralLinearGroup (Fin (n + 1)) R) =
        colHom n w := by
    have h_eq : (↑(colSubgroupHom n v) :
        Matrix.GeneralLinearGroup (Fin (n + 1)) R) =
        ↑(colSubgroupHom n w) :=
      congrArg Subtype.val h
    simpa [colSubgroupHom] using h_eq
  exact colHom_injective n h_val

private lemma rowSubgroupHom_injective (n : ℕ) :
    Function.Injective (rowSubgroupHom (R := R) n) := by
  intro v w h
  have h_val :
      (rowHom n v : Matrix.GeneralLinearGroup (Fin (n + 1)) R) =
        rowHom n w := by
    have h_eq : (↑(rowSubgroupHom n v) :
        Matrix.GeneralLinearGroup (Fin (n + 1)) R) =
        ↑(rowSubgroupHom n w) :=
      congrArg Subtype.val h
    simpa [rowSubgroupHom] using h_eq
  exact rowHom_injective n h_val

private lemma colStableHom_injective (n : ℕ) :
    Function.Injective (colStableHom (R := R) n) := by
  intro v w h
  have h_inj :=
    AlgebraicKTheory.StableE.fromFinite_injective (R := R) (n + 1)
  have h_eq : colSubgroupHom n v = colSubgroupHom n w := h_inj h
  exact colSubgroupHom_injective n h_eq

private lemma rowStableHom_injective (n : ℕ) :
    Function.Injective (rowStableHom (R := R) n) := by
  intro v w h
  have h_inj :=
    AlgebraicKTheory.StableE.fromFinite_injective (R := R) (n + 1)
  have h_eq : rowSubgroupHom n v = rowSubgroupHom n w := h_inj h
  exact rowSubgroupHom_injective n h_eq

private lemma colStableHom_single (n : ℕ) (i : Fin n)
    (a : Multiplicative R) :
    colStableHom n (Pi.mulSingle i a) =
      AlgebraicKTheory.StableE.natElementary (R := R)
        i.val n (Nat.ne_of_lt i.isLt) a.toAdd := by
  have h_ce := colHom_single n i a
  have h_sub_eq :
      colSubgroupHom n (Pi.mulSingle i a) =
        Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
          (colEquiv n (Sum.inl i))
          (colEquiv n (Sum.inr (0 : Fin 1)))
          (colHij_neq n i) a.toAdd := by
    apply Subtype.ext
    simp only [Matrix.GeneralLinearGroup.ElementarySubgroup.coe_elementary,
      colSubgroupHom, MonoidHom.codRestrict_apply]
    exact h_ce
  have h_from :
      colStableHom n (Pi.mulSingle i a) =
        AlgebraicKTheory.StableE.elementary (n + 1)
          (colEquiv n (Sum.inl i))
          (colEquiv n (Sum.inr (0 : Fin 1)))
          (colHij_neq n i) a.toAdd := by
    calc colStableHom n (Pi.mulSingle i a)
        = AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
            (colSubgroupHom n (Pi.mulSingle i a)) := rfl
      _ = AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
            (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
              (colEquiv n (Sum.inl i))
              (colEquiv n (Sum.inr (0 : Fin 1)))
              (colHij_neq n i) a.toAdd) := by rw [h_sub_eq]
      _ = AlgebraicKTheory.StableE.elementary (n + 1)
            (colEquiv n (Sum.inl i))
            (colEquiv n (Sum.inr (0 : Fin 1)))
            (colHij_neq n i) a.toAdd := by
          rw [AlgebraicKTheory.StableE.fromFinite_elementary]
  rw [h_from]
  have h_left : colEquiv n (Sum.inl i) = Fin.castAdd 1 i := by
    simp [colEquiv, finSumFinEquiv_apply_left]
  have h_right : colEquiv n (Sum.inr (0 : Fin 1)) = Fin.natAdd n 0 := by
    simp [colEquiv, finSumFinEquiv_apply_right]
  have h1 : Fin.castAdd (1 : ℕ) i = ⟨i.val, Nat.lt_add_right 1 i.isLt⟩ := by
    apply Fin.ext; rfl
  have h2 : Fin.natAdd n (0 : Fin 1) = ⟨n, Nat.lt_succ_self n⟩ := by
    apply Fin.ext
    simp [Fin.natAdd]
  have h_elem :
      AlgebraicKTheory.StableE.elementary (n + 1)
        (colEquiv n (Sum.inl i))
        (colEquiv n (Sum.inr (0 : Fin 1)))
        (colHij_neq n i) a.toAdd =
      AlgebraicKTheory.StableE.elementary (n + 1)
        ⟨i.val, Nat.lt_add_right 1 i.isLt⟩
        ⟨n, Nat.lt_succ_self n⟩
        (by intro h; exact Nat.ne_of_lt i.isLt (congrArg Fin.val h)) a.toAdd := by
    apply Subtype.ext
    simp only [AlgebraicKTheory.StableE.coe_elementary, h_left, h_right, h1, h2]
  rw [h_elem]
  rw [← AlgebraicKTheory.StableE.natElementary_fin]

private lemma rowStableHom_single (n : ℕ) (i : Fin n)
    (a : Multiplicative R) :
    rowStableHom n (Pi.mulSingle i a) =
      AlgebraicKTheory.StableE.natElementary (R := R)
        n i.val (Ne.symm (Nat.ne_of_lt i.isLt)) a.toAdd := by
  have h_ce := rowHom_single n i a
  have h_sub_eq :
      rowSubgroupHom n (Pi.mulSingle i a) =
        Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
          (colEquiv n (Sum.inr (0 : Fin 1)))
          (colEquiv n (Sum.inl i))
          (rowHij_neq n i) a.toAdd := by
    apply Subtype.ext
    simp only [Matrix.GeneralLinearGroup.ElementarySubgroup.coe_elementary,
      rowSubgroupHom, MonoidHom.codRestrict_apply]
    exact h_ce
  have h_from :
      rowStableHom n (Pi.mulSingle i a) =
        AlgebraicKTheory.StableE.elementary (n + 1)
          (colEquiv n (Sum.inr (0 : Fin 1)))
          (colEquiv n (Sum.inl i))
          (rowHij_neq n i) a.toAdd := by
    calc rowStableHom n (Pi.mulSingle i a)
        = AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
            (rowSubgroupHom n (Pi.mulSingle i a)) := rfl
      _ = AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
            (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
              (colEquiv n (Sum.inr (0 : Fin 1)))
              (colEquiv n (Sum.inl i))
              (rowHij_neq n i) a.toAdd) := by rw [h_sub_eq]
      _ = AlgebraicKTheory.StableE.elementary (n + 1)
            (colEquiv n (Sum.inr (0 : Fin 1)))
            (colEquiv n (Sum.inl i))
            (rowHij_neq n i) a.toAdd := by
          rw [AlgebraicKTheory.StableE.fromFinite_elementary]
  rw [h_from]
  have h_left : colEquiv n (Sum.inr (0 : Fin 1)) = Fin.natAdd n 0 := by
    simp [colEquiv, finSumFinEquiv_apply_right]
  have h_right : colEquiv n (Sum.inl i) = Fin.castAdd 1 i := by
    simp [colEquiv, finSumFinEquiv_apply_left]
  have h1 : Fin.natAdd n (0 : Fin 1) = ⟨n, Nat.lt_succ_self n⟩ := by
    apply Fin.ext
    simp [Fin.natAdd]
  have h2 : Fin.castAdd (1 : ℕ) i = ⟨i.val, Nat.lt_add_right 1 i.isLt⟩ := by
    apply Fin.ext; rfl
  have h_elem :
      AlgebraicKTheory.StableE.elementary (n + 1)
        (colEquiv n (Sum.inr (0 : Fin 1)))
        (colEquiv n (Sum.inl i))
        (rowHij_neq n i) a.toAdd =
      AlgebraicKTheory.StableE.elementary (n + 1)
        ⟨n, Nat.lt_succ_self n⟩
        ⟨i.val, Nat.lt_add_right 1 i.isLt⟩
        (by intro h; exact Nat.ne_of_lt i.isLt (congrArg Fin.val h.symm)) a.toAdd := by
    apply Subtype.ext
    simp only [AlgebraicKTheory.StableE.coe_elementary, h_left, h_right, h1, h2]
  rw [h_elem]
  rw [← AlgebraicKTheory.StableE.natElementary_fin]

private lemma steinHomCol_single (n : ℕ) (i : Fin n)
    (a : Multiplicative R) :
    (AlgebraicKTheory.StableSteinberg.toStableE (R := R)).comp
        (AlgebraicKTheory.StableSteinberg.lastColumnProduct (R := R) n)
        (Pi.mulSingle i a) =
      AlgebraicKTheory.StableE.natElementary (R := R)
        i.val n (Nat.ne_of_lt i.isLt) a.toAdd := by
  simp [AlgebraicKTheory.StableSteinberg.lastColumnProduct_mulSingle,
    AlgebraicKTheory.StableSteinberg.toStableE_x]

private lemma steinHomRow_single (n : ℕ) (i : Fin n)
    (a : Multiplicative R) :
    (AlgebraicKTheory.StableSteinberg.toStableE (R := R)).comp
        (AlgebraicKTheory.StableSteinberg.lastRowProduct (R := R) n)
        (Pi.mulSingle i a) =
      AlgebraicKTheory.StableE.natElementary (R := R)
        n i.val (Ne.symm (Nat.ne_of_lt i.isLt)) a.toAdd := by
  simp [AlgebraicKTheory.StableSteinberg.lastRowProduct_mulSingle,
    AlgebraicKTheory.StableSteinberg.toStableE_x]

private lemma steinHomCol_eq_colStableHom (n : ℕ) :
    (AlgebraicKTheory.StableSteinberg.toStableE (R := R)).comp
        (AlgebraicKTheory.StableSteinberg.lastColumnProduct (R := R) n) =
      colStableHom n := by
  apply MonoidHom.pi_ext
  intro i a
  rw [steinHomCol_single, colStableHom_single]

private lemma steinHomRow_eq_rowStableHom (n : ℕ) :
    (AlgebraicKTheory.StableSteinberg.toStableE (R := R)).comp
        (AlgebraicKTheory.StableSteinberg.lastRowProduct (R := R) n) =
      rowStableHom n := by
  apply MonoidHom.pi_ext
  intro i a
  rw [steinHomRow_single, rowStableHom_single]

/-- `toStableE` is injective on the last-column root subgroup. -/
public theorem toStableE_injOn_lastColumnSubgroup (n : ℕ) :
    Set.InjOn (AlgebraicKTheory.StableSteinberg.toStableE (R := R))
      ↑(AlgebraicKTheory.StableSteinberg.lastColumnSubgroup (R := R) n) := by
  intro x hx y hy h_eq
  have h_range :
      (AlgebraicKTheory.StableSteinberg.lastColumnProduct (R := R) n).range =
        AlgebraicKTheory.StableSteinberg.lastColumnSubgroup (R := R) n :=
    AlgebraicKTheory.StableSteinberg.lastColumnProduct_range n
  have hx_mem :
      x ∈ (AlgebraicKTheory.StableSteinberg.lastColumnProduct (R := R) n).range :=
    h_range ▸ hx
  have hy_mem :
      y ∈ (AlgebraicKTheory.StableSteinberg.lastColumnProduct (R := R) n).range :=
    h_range ▸ hy
  obtain ⟨vx, hvx⟩ := hx_mem
  obtain ⟨vy, hvy⟩ := hy_mem
  have h_comp := steinHomCol_eq_colStableHom (R := R) n
  have h_inj := colStableHom_injective (R := R) n
  have h1 :
      AlgebraicKTheory.StableSteinberg.toStableE
        (AlgebraicKTheory.StableSteinberg.lastColumnProduct n vx) =
      AlgebraicKTheory.StableSteinberg.toStableE
        (AlgebraicKTheory.StableSteinberg.lastColumnProduct n vy) := by
    calc AlgebraicKTheory.StableSteinberg.toStableE
            (AlgebraicKTheory.StableSteinberg.lastColumnProduct n vx)
        = AlgebraicKTheory.StableSteinberg.toStableE x := by rw [hvx]
      _ = AlgebraicKTheory.StableSteinberg.toStableE y := h_eq
      _ = AlgebraicKTheory.StableSteinberg.toStableE
            (AlgebraicKTheory.StableSteinberg.lastColumnProduct n vy) := by
          rw [hvy]
  have h2 :
      (AlgebraicKTheory.StableSteinberg.toStableE.comp
        (AlgebraicKTheory.StableSteinberg.lastColumnProduct n)) vx =
      (AlgebraicKTheory.StableSteinberg.toStableE.comp
        (AlgebraicKTheory.StableSteinberg.lastColumnProduct n)) vy := by
    simpa using h1
  rw [h_comp] at h2
  have h3 : vx = vy := h_inj h2
  calc x = AlgebraicKTheory.StableSteinberg.lastColumnProduct n vx := hvx.symm
    _ = AlgebraicKTheory.StableSteinberg.lastColumnProduct n vy := by rw [h3]
    _ = y := hvy

/-- `toStableE` is injective on the last-row root subgroup. -/
public theorem toStableE_injOn_lastRowSubgroup (n : ℕ) :
    Set.InjOn (AlgebraicKTheory.StableSteinberg.toStableE (R := R))
      ↑(AlgebraicKTheory.StableSteinberg.lastRowSubgroup (R := R) n) := by
  intro x hx y hy h_eq
  have h_range :
      (AlgebraicKTheory.StableSteinberg.lastRowProduct (R := R) n).range =
        AlgebraicKTheory.StableSteinberg.lastRowSubgroup (R := R) n :=
    AlgebraicKTheory.StableSteinberg.lastRowProduct_range n
  have hx_mem :
      x ∈ (AlgebraicKTheory.StableSteinberg.lastRowProduct (R := R) n).range :=
    h_range ▸ hx
  have hy_mem :
      y ∈ (AlgebraicKTheory.StableSteinberg.lastRowProduct (R := R) n).range :=
    h_range ▸ hy
  obtain ⟨vx, hvx⟩ := hx_mem
  obtain ⟨vy, hvy⟩ := hy_mem
  have h_comp := steinHomRow_eq_rowStableHom (R := R) n
  have h_inj := rowStableHom_injective (R := R) n
  have h1 :
      AlgebraicKTheory.StableSteinberg.toStableE
        (AlgebraicKTheory.StableSteinberg.lastRowProduct n vx) =
      AlgebraicKTheory.StableSteinberg.toStableE
        (AlgebraicKTheory.StableSteinberg.lastRowProduct n vy) := by
    calc AlgebraicKTheory.StableSteinberg.toStableE
            (AlgebraicKTheory.StableSteinberg.lastRowProduct n vx)
        = AlgebraicKTheory.StableSteinberg.toStableE x := by rw [hvx]
      _ = AlgebraicKTheory.StableSteinberg.toStableE y := h_eq
      _ = AlgebraicKTheory.StableSteinberg.toStableE
            (AlgebraicKTheory.StableSteinberg.lastRowProduct n vy) := by
          rw [hvy]
  have h2 :
      (AlgebraicKTheory.StableSteinberg.toStableE.comp
        (AlgebraicKTheory.StableSteinberg.lastRowProduct n)) vx =
      (AlgebraicKTheory.StableSteinberg.toStableE.comp
        (AlgebraicKTheory.StableSteinberg.lastRowProduct n)) vy := by
    simpa using h1
  rw [h_comp] at h2
  have h3 : vx = vy := h_inj h2
  calc x = AlgebraicKTheory.StableSteinberg.lastRowProduct n vx := hvx.symm
    _ = AlgebraicKTheory.StableSteinberg.lastRowProduct n vy := by rw [h3]
    _ = y := hvy

/-! ## General last-boundary forcing -/

private noncomputable def liftToSucc (n : ℕ)
    (g : Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R) :
    Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) R :=
  ⟨Matrix.GeneralLinearGroup.blockStabilization n 1 R (↑g : Matrix.GeneralLinearGroup (Fin n) R),
    by
      have h1 : (↑g : Matrix.GeneralLinearGroup (Fin n) R) ∈
          Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R := g.prop
      have hBd : Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin 1) R
          (↑g : Matrix.GeneralLinearGroup (Fin n) R) ∈
          Matrix.GeneralLinearGroup.elementarySubgroup (Fin n ⊕ Fin 1) R :=
        BlockElementary.blockDiagonalOne_mem_elementarySubgroup h1
      have hRe : Matrix.GeneralLinearGroup.reindexMulEquiv (colEquiv n)
          (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin 1) R
            (↑g : Matrix.GeneralLinearGroup (Fin n) R)) ∈
          Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) R :=
        Matrix.GeneralLinearGroup.reindexMulEquiv_mem_elementarySubgroup (colEquiv n) hBd
      have hEq : Matrix.GeneralLinearGroup.blockStabilization n 1 R
          (↑g : Matrix.GeneralLinearGroup (Fin n) R) =
          Matrix.GeneralLinearGroup.reindexMulEquiv (colEquiv n)
            (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin 1) R
              (↑g : Matrix.GeneralLinearGroup (Fin n) R)) := rfl
      rw [hEq]
      exact hRe⟩

private lemma fromFinite_lift_eq (n : ℕ)
    (g : Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R) :
    AlgebraicKTheory.StableE.fromFinite (R := R) n g =
      AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1) (liftToSucc (R := R) n g) := by
  apply Subtype.ext
  calc (↑(AlgebraicKTheory.StableE.fromFinite (R := R) n g) :
        AlgebraicKTheory.StableGL R)
      = AlgebraicKTheory.StableGL.of (↑g : Matrix.GeneralLinearGroup (Fin n) R) := rfl
    _ = AlgebraicKTheory.StableGL.of
          (Matrix.GeneralLinearGroup.blockStabilization n 1 R
            (↑g : Matrix.GeneralLinearGroup (Fin n) R)) := by
        rw [← AlgebraicKTheory.StableGL.of_blockStabilization]
    _ = AlgebraicKTheory.StableGL.of
          (↑(liftToSucc (R := R) n g) :
            Matrix.GeneralLinearGroup (Fin (n + 1)) R) := rfl
    _ = ↑(AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1) (liftToSucc n g)) := rfl

/-- Smallest sound general forcing theorem.
If `toStableE (lastColumnProduct c * lastRowProduct r)` already lies in
`E_n`'s stable range, then `c = 1` and `r = 1`. Uniform for `n = 0`;
`[Ring R]` only; no determinant/field/product-one hypothesis;
no kernel equality claim. -/
public theorem toStableE_lastColumnRow_product_mem_range_imp_eq_one
    (n : ℕ) (c r : Fin n → Multiplicative R)
    (h : AlgebraicKTheory.StableSteinberg.toStableE
        (AlgebraicKTheory.StableSteinberg.lastColumnProduct (R := R) n c *
         AlgebraicKTheory.StableSteinberg.lastRowProduct (R := R) n r) ∈
         (AlgebraicKTheory.StableE.fromFinite (R := R) n).range) :
    c = 1 ∧ r = 1 := by
  obtain ⟨gN, hgN⟩ := MonoidHom.mem_range.mp h
  have hColComp : AlgebraicKTheory.StableSteinberg.toStableE
        (AlgebraicKTheory.StableSteinberg.lastColumnProduct (R := R) n c) =
      colStableHom (R := R) n c := by
    have h := steinHomCol_eq_colStableHom (R := R) n
    have h1 : (AlgebraicKTheory.StableSteinberg.toStableE.comp
        (AlgebraicKTheory.StableSteinberg.lastColumnProduct n)) c =
        colStableHom (R := R) n c := by rw [h]
    simpa [MonoidHom.comp_apply] using h1
  have hRowComp : AlgebraicKTheory.StableSteinberg.toStableE
        (AlgebraicKTheory.StableSteinberg.lastRowProduct (R := R) n r) =
      rowStableHom (R := R) n r := by
    have h := steinHomRow_eq_rowStableHom (R := R) n
    have h1 : (AlgebraicKTheory.StableSteinberg.toStableE.comp
        (AlgebraicKTheory.StableSteinberg.lastRowProduct n)) r =
        rowStableHom (R := R) n r := by rw [h]
    simpa [MonoidHom.comp_apply] using h1
  have hProdMul : AlgebraicKTheory.StableSteinberg.toStableE
        (AlgebraicKTheory.StableSteinberg.lastColumnProduct n c *
         AlgebraicKTheory.StableSteinberg.lastRowProduct n r) =
      AlgebraicKTheory.StableSteinberg.toStableE
        (AlgebraicKTheory.StableSteinberg.lastColumnProduct n c) *
      AlgebraicKTheory.StableSteinberg.toStableE
        (AlgebraicKTheory.StableSteinberg.lastRowProduct n r) := by
    rw [map_mul]
  have hCR : AlgebraicKTheory.StableSteinberg.toStableE
        (AlgebraicKTheory.StableSteinberg.lastColumnProduct n c *
         AlgebraicKTheory.StableSteinberg.lastRowProduct n r) =
      AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
        (colSubgroupHom (R := R) n c * rowSubgroupHom (R := R) n r) := by
    calc AlgebraicKTheory.StableSteinberg.toStableE
          (AlgebraicKTheory.StableSteinberg.lastColumnProduct n c *
           AlgebraicKTheory.StableSteinberg.lastRowProduct n r)
        = colStableHom (R := R) n c * rowStableHom (R := R) n r := by
          rw [hProdMul, hColComp, hRowComp]
      _ = AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
              (colSubgroupHom (R := R) n c) *
          AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
              (rowSubgroupHom (R := R) n r) := rfl
      _ = AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
            (colSubgroupHom (R := R) n c * rowSubgroupHom (R := R) n r) := by
          rw [← map_mul]
  let S : Matrix.GeneralLinearGroup (Fin n) R := ↑gN
  let liftSucc : Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) R :=
    liftToSucc (R := R) n gN
  have hLiftEq : AlgebraicKTheory.StableE.fromFinite (R := R) n gN =
      AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1) liftSucc :=
    fromFinite_lift_eq (R := R) n gN
  have hEqSucc : AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
        (colSubgroupHom (R := R) n c * rowSubgroupHom (R := R) n r) =
      AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1) liftSucc := by
    calc AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
          (colSubgroupHom n c * rowSubgroupHom n r)
        = AlgebraicKTheory.StableSteinberg.toStableE
            (AlgebraicKTheory.StableSteinberg.lastColumnProduct n c *
             AlgebraicKTheory.StableSteinberg.lastRowProduct n r) := hCR.symm
      _ = AlgebraicKTheory.StableE.fromFinite (R := R) n gN := hgN.symm
      _ = AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1) liftSucc := hLiftEq
  have hInj := AlgebraicKTheory.StableE.fromFinite_injective (R := R) (n + 1)
  have hSubEq : colSubgroupHom (R := R) n c * rowSubgroupHom (R := R) n r = liftSucc :=
    hInj hEqSucc
  have h_gCR_val : (↑(colSubgroupHom (R := R) n c * rowSubgroupHom (R := R) n r) :
      Matrix.GeneralLinearGroup (Fin (n + 1)) R) =
      colGL (R := R) n c * rowGL (R := R) n r := rfl
  have h_lift_val : (↑liftSucc : Matrix.GeneralLinearGroup (Fin (n + 1)) R) =
      Matrix.GeneralLinearGroup.blockStabilization n 1 R S := rfl
  have hGLEq : colGL (R := R) n c * rowGL (R := R) n r =
      Matrix.GeneralLinearGroup.blockStabilization n 1 R S := by
    calc colGL n c * rowGL n r
        = ↑(colSubgroupHom n c * rowSubgroupHom n r) := h_gCR_val.symm
      _ = ↑liftSucc := congrArg Subtype.val hSubEq
      _ = Matrix.GeneralLinearGroup.blockStabilization n 1 R S := h_lift_val
  have h_col_re : colGL (R := R) n c =
      Matrix.GeneralLinearGroup.reindexMulEquiv (colEquiv n)
        (BlockElementary.upperUnit (colMatrix n c)) := rfl
  have h_row_re : rowGL (R := R) n r =
      Matrix.GeneralLinearGroup.reindexMulEquiv (colEquiv n)
        (BlockElementary.lowerUnit (rowMatrix n r)) := rfl
  have h_stab_re : Matrix.GeneralLinearGroup.blockStabilization n 1 R S =
      Matrix.GeneralLinearGroup.reindexMulEquiv (colEquiv n)
        (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin 1) R S) := rfl
  have hProdRe : colGL (R := R) n c * rowGL (R := R) n r =
      Matrix.GeneralLinearGroup.reindexMulEquiv (colEquiv n)
        (BlockElementary.upperUnit (colMatrix n c) *
         BlockElementary.lowerUnit (rowMatrix n r)) := by
    calc colGL n c * rowGL n r
        = Matrix.GeneralLinearGroup.reindexMulEquiv (colEquiv n)
            (BlockElementary.upperUnit (colMatrix n c)) *
          Matrix.GeneralLinearGroup.reindexMulEquiv (colEquiv n)
            (BlockElementary.lowerUnit (rowMatrix n r)) := by
          rw [h_col_re, h_row_re]
      _ = Matrix.GeneralLinearGroup.reindexMulEquiv (colEquiv n)
            (BlockElementary.upperUnit (colMatrix n c) *
             BlockElementary.lowerUnit (rowMatrix n r)) := by
          rw [← MulEquiv.map_mul]
  have hReEq : Matrix.GeneralLinearGroup.reindexMulEquiv (colEquiv n)
        (BlockElementary.upperUnit (colMatrix n c) *
         BlockElementary.lowerUnit (rowMatrix n r)) =
      Matrix.GeneralLinearGroup.reindexMulEquiv (colEquiv n)
        (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin 1) R S) := by
    calc Matrix.GeneralLinearGroup.reindexMulEquiv (colEquiv n)
          (BlockElementary.upperUnit (colMatrix n c) *
           BlockElementary.lowerUnit (rowMatrix n r))
        = colGL n c * rowGL n r := hProdRe.symm
      _ = Matrix.GeneralLinearGroup.blockStabilization n 1 R S := hGLEq
      _ = Matrix.GeneralLinearGroup.reindexMulEquiv (colEquiv n)
            (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin 1) R S) := h_stab_re.symm
  have hUL : BlockElementary.upperUnit (colMatrix n c) *
      BlockElementary.lowerUnit (rowMatrix n r) =
      Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin 1) R S :=
    (MulEquiv.injective (Matrix.GeneralLinearGroup.reindexMulEquiv (colEquiv n))) hReEq
  -- force off-diagonal blocks to zero via weakBlockLDU
  let fOne := Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin 1) R
  have hOneEq : BlockElementary.upperUnit (colMatrix n c) *
      BlockElementary.lowerUnit (rowMatrix n r) *
      fOne S⁻¹ = 1 := by
    calc BlockElementary.upperUnit (colMatrix n c) *
          BlockElementary.lowerUnit (rowMatrix n r) *
          fOne S⁻¹
        = fOne S * fOne S⁻¹ := by rw [hUL]
      _ = fOne (S * S⁻¹) := by rw [← fOne.map_mul]
      _ = fOne 1 := by rw [mul_inv_cancel]
      _ = 1 := by rw [fOne.map_one]
  have hDiag11 : BlockElementary.blockDiagonal
        (1 : Matrix.GeneralLinearGroup (Fin n) R)
        (1 : Matrix.GeneralLinearGroup (Fin 1) R) = 1 := by
    apply Units.ext
    simp [BlockElementary.coe_blockDiagonal, Matrix.fromBlocks_one]
  have hWeakPrem : BlockElementary.upperUnit (colMatrix n c) *
      BlockElementary.blockDiagonal (1 : Matrix.GeneralLinearGroup (Fin n) R)
        (1 : Matrix.GeneralLinearGroup (Fin 1) R) *
      BlockElementary.lowerUnit (rowMatrix n r) *
      fOne S⁻¹ = 1 := by
    calc BlockElementary.upperUnit (colMatrix n c) *
          BlockElementary.blockDiagonal 1 1 *
          BlockElementary.lowerUnit (rowMatrix n r) *
          fOne S⁻¹
        = BlockElementary.upperUnit (colMatrix n c) * 1 *
          BlockElementary.lowerUnit (rowMatrix n r) *
          fOne S⁻¹ := by rw [hDiag11]
      _ = BlockElementary.upperUnit (colMatrix n c) *
          BlockElementary.lowerUnit (rowMatrix n r) *
          fOne S⁻¹ := by simp [mul_one]
      _ = 1 := hOneEq
  have hWeak := BlockElementary.weakBlockLDU_eq_one (R := R) (n := n) hWeakPrem
  obtain ⟨hB_zero, hC_zero, _, _⟩ := hWeak
  have hc : c = 1 := by
    funext i
    have hB : colMatrix (R := R) n c = 0 := hB_zero
    have h_entry : (colMatrix (R := R) n c) i (0 : Fin 1) = (0 : R) := by
      calc (colMatrix n c) i (0 : Fin 1)
          = (0 : Matrix (Fin n) (Fin 1) R) i (0 : Fin 1) := by rw [hB]
        _ = 0 := rfl
    simp only [colMatrix, Matrix.of_apply] at h_entry
    calc c i = Multiplicative.ofAdd ((c i).toAdd) := rfl
      _ = Multiplicative.ofAdd (0 : R) := by rw [h_entry]
      _ = 1 := rfl
  have hr : r = 1 := by
    funext i
    have hC : rowMatrix (R := R) n r = 0 := hC_zero
    have h_entry : (rowMatrix (R := R) n r) (0 : Fin 1) i = (0 : R) := by
      calc (rowMatrix n r) (0 : Fin 1) i
          = (0 : Matrix (Fin 1) (Fin n) R) (0 : Fin 1) i := by rw [hC]
        _ = 0 := rfl
    simp only [rowMatrix, Matrix.of_apply] at h_entry
    calc r i = Multiplicative.ofAdd ((r i).toAdd) := rfl
      _ = Multiplicative.ofAdd (0 : R) := by rw [h_entry]
      _ = 1 := rfl
  exact ⟨hc, hr⟩

/-! ## Finite last-boundary-block evaluation

Public `n+1` finite elementary representatives for `lastBoundaryBlock n`.
Generic ring `R`, arbitrary universe `u`, orientation-preserving
`inl = column = upper` and `inr = row = lower` at the last boundary index. -/

/-- Finite elementary representative of a single last-boundary block at rank
`n+1` over an arbitrary ring `R` (universe `u`).

Orientation: `Sum.inl c` is the last-column block (upper unit),
`Sum.inr r` is the last-row block (lower unit). Dispatches to the private
`colSubgroupHom n` and `rowSubgroupHom n` subgroup homs, reusing their
`BlockElementary` block machinery. Finite rank is exactly `n+1`.

Proves evaluation only; makes no pivot, scalar-equation, alternation,
kernel-generation, finite-stage landing, strict-decrease, cocycle,
naturality, or Matsumoto claim. -/
public noncomputable def lastBoundaryBlockElementary (n : ℕ)
    (b : Sum (Fin n → Multiplicative R) (Fin n → Multiplicative R)) :
    Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) R :=
  match b with
  | Sum.inl c => colSubgroupHom n c
  | Sum.inr r => rowSubgroupHom n r

/-- Coercion of the column (`inl`) elementary representative to
`Matrix.GeneralLinearGroup (Fin (n+1)) R` equals the public block
construction with `finSumFinEquiv` and `BlockElementary.upperUnit`.

Finite rank `n+1`, generic ring `R` (universe `u`), orientation
`inl = column = upper`. Right side uses only public names
(`reindexMulEquiv`, `finSumFinEquiv`, `BlockElementary.upperUnit`,
`Matrix.of`); no private `colMatrix`/`colEquiv`/`colGL` appears.

Proves evaluation only; makes no pivot, scalar-equation, alternation,
kernel-generation, finite-stage landing, strict-decrease, cocycle,
naturality, or Matsumoto claim. -/
public theorem lastBoundaryBlockElementary_inl_val (n : ℕ)
    (c : Fin n → Multiplicative R) :
    (↑(lastBoundaryBlockElementary n (Sum.inl c)) :
      Matrix.GeneralLinearGroup (Fin (n + 1)) R) =
    reindexMulEquiv (finSumFinEquiv (m := n) (n := 1))
      (BlockElementary.upperUnit (Matrix.of fun i _ => (c i).toAdd)) := by
  have h_eq : colMatrix n c = Matrix.of fun i _ => (c i).toAdd := by
    ext i j
    simp [colMatrix, Matrix.of_apply]
  have h_re : colEquiv n = finSumFinEquiv (m := n) (n := 1) := rfl
  calc (↑(lastBoundaryBlockElementary n (Sum.inl c)) :
        Matrix.GeneralLinearGroup (Fin (n + 1)) R)
      = colHom n c := by
        simp [lastBoundaryBlockElementary, colSubgroupHom]
    _ = colGL n c := rfl
    _ = reindexMulEquiv (colEquiv n)
          (BlockElementary.upperUnit (colMatrix n c)) := rfl
    _ = reindexMulEquiv (finSumFinEquiv (m := n) (n := 1))
          (BlockElementary.upperUnit (Matrix.of fun i _ => (c i).toAdd)) := by
        rw [h_re, h_eq]

/-- Coercion of the row (`inr`) elementary representative to
`Matrix.GeneralLinearGroup (Fin (n+1)) R` equals the public block
construction with `finSumFinEquiv` and `BlockElementary.lowerUnit`.

Finite rank `n+1`, generic ring `R` (universe `u`), orientation
`inr = row = lower`. Right side uses only public names
(`reindexMulEquiv`, `finSumFinEquiv`, `BlockElementary.lowerUnit`,
`Matrix.of`); no private `rowMatrix`/`colEquiv`/`rowGL` appears.

Proves evaluation only; makes no pivot, scalar-equation, alternation,
kernel-generation, finite-stage landing, strict-decrease, cocycle,
naturality, or Matsumoto claim. -/
public theorem lastBoundaryBlockElementary_inr_val (n : ℕ)
    (r : Fin n → Multiplicative R) :
    (↑(lastBoundaryBlockElementary n (Sum.inr r)) :
      Matrix.GeneralLinearGroup (Fin (n + 1)) R) =
    reindexMulEquiv (finSumFinEquiv (m := n) (n := 1))
      (BlockElementary.lowerUnit (Matrix.of fun _ j => (r j).toAdd)) := by
  have h_eq : rowMatrix n r = Matrix.of fun _ j => (r j).toAdd := by
    ext i j
    simp [rowMatrix, Matrix.of_apply]
  have h_re : colEquiv n = finSumFinEquiv (m := n) (n := 1) := rfl
  calc (↑(lastBoundaryBlockElementary n (Sum.inr r)) :
        Matrix.GeneralLinearGroup (Fin (n + 1)) R)
      = rowHom n r := by
        simp [lastBoundaryBlockElementary, rowSubgroupHom]
    _ = rowGL n r := rfl
    _ = reindexMulEquiv (colEquiv n)
          (BlockElementary.lowerUnit (rowMatrix n r)) := rfl
    _ = reindexMulEquiv (finSumFinEquiv (m := n) (n := 1))
          (BlockElementary.lowerUnit (Matrix.of fun _ j => (r j).toAdd)) := by
        rw [h_re, h_eq]

private abbrev coeffToBlock (n : ℕ) :
    Sum (Fin n → Multiplicative R) (Fin n → Multiplicative R) →
      Matrix (Fin n) (Fin 1) R ⊕ Matrix (Fin 1) (Fin n) R :=
  Sum.elim (fun c => Sum.inl (Matrix.of fun i _ => (c i).toAdd))
    (fun r => Sum.inr (Matrix.of fun _ j => (r j).toAdd))

private lemma lastBoundaryBlockElementary_val (n : ℕ)
    (b : Sum (Fin n → Multiplicative R) (Fin n → Multiplicative R)) :
    (↑(lastBoundaryBlockElementary (R := R) n b) :
      Matrix.GeneralLinearGroup (Fin (n + 1)) R) =
    Matrix.GeneralLinearGroup.reindexMulEquiv (finSumFinEquiv (m := n) (n := 1))
      (Sum.elim Matrix.GeneralLinearGroup.BlockElementary.upperUnit
        Matrix.GeneralLinearGroup.BlockElementary.lowerUnit
        (coeffToBlock (R := R) n b)) := by
  cases b with
  | inl c =>
    have h : coeffToBlock (R := R) n (Sum.inl c) =
        Sum.inl (Matrix.of fun i _ => (c i).toAdd) := rfl
    rw [h]
    exact lastBoundaryBlockElementary_inl_val (R := R) n c
  | inr r =>
    have h : coeffToBlock (R := R) n (Sum.inr r) =
        Sum.inr (Matrix.of fun _ j => (r j).toAdd) := rfl
    rw [h]
    exact lastBoundaryBlockElementary_inr_val (R := R) n r

/-- Evaluation of a single last-boundary block via `toStableE` equals the
stable elementary evaluation of its finite `n+1` representative.

Finite rank `n+1`, generic ring `R` (universe `u`), both orientations
`inl = column` and `inr = row`. Proved by cases on `b` and the private
`steinHomCol_eq_colStableHom` / `steinHomRow_eq_rowStableHom` chain,
reusing the existing finite block machinery.

Proves evaluation only; makes no pivot, scalar-equation, alternation,
kernel-generation, finite-stage landing, strict-decrease, cocycle,
naturality, or Matsumoto claim. -/
public theorem toStableE_lastBoundaryBlock (n : ℕ)
    (b : Sum (Fin n → Multiplicative R) (Fin n → Multiplicative R)) :
    AlgebraicKTheory.StableSteinberg.toStableE
        (AlgebraicKTheory.StableSteinberg.lastBoundaryBlock (R := R) n b) =
      AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
        (lastBoundaryBlockElementary n b) := by
  cases b with
  | inl c =>
    have h_col : AlgebraicKTheory.StableSteinberg.lastBoundaryBlock
        (R := R) n (Sum.inl c) =
        AlgebraicKTheory.StableSteinberg.lastColumnProduct n c := by
      simp [AlgebraicKTheory.StableSteinberg.lastBoundaryBlock]
    have h_toCol :
        AlgebraicKTheory.StableSteinberg.toStableE
            (AlgebraicKTheory.StableSteinberg.lastColumnProduct
              (R := R) n c) =
          colStableHom (R := R) n c := by
      have h := steinHomCol_eq_colStableHom (R := R) n
      have h1 : (AlgebraicKTheory.StableSteinberg.toStableE.comp
          (AlgebraicKTheory.StableSteinberg.lastColumnProduct n)) c =
          colStableHom (R := R) n c := by rw [h]
      simpa [MonoidHom.comp_apply] using h1
    calc AlgebraicKTheory.StableSteinberg.toStableE
          (AlgebraicKTheory.StableSteinberg.lastBoundaryBlock (R := R) n
            (Sum.inl c))
        = AlgebraicKTheory.StableSteinberg.toStableE
            (AlgebraicKTheory.StableSteinberg.lastColumnProduct n c) := by
          rw [h_col]
      _ = colStableHom (R := R) n c := h_toCol
      _ = AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
            (colSubgroupHom n c) := rfl
      _ = AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
            (lastBoundaryBlockElementary n (Sum.inl c)) := rfl
  | inr r =>
    have h_row : AlgebraicKTheory.StableSteinberg.lastBoundaryBlock
        (R := R) n (Sum.inr r) =
        AlgebraicKTheory.StableSteinberg.lastRowProduct n r := by
      simp [AlgebraicKTheory.StableSteinberg.lastBoundaryBlock]
    have h_toRow :
        AlgebraicKTheory.StableSteinberg.toStableE
            (AlgebraicKTheory.StableSteinberg.lastRowProduct
              (R := R) n r) =
          rowStableHom (R := R) n r := by
      have h := steinHomRow_eq_rowStableHom (R := R) n
      have h1 : (AlgebraicKTheory.StableSteinberg.toStableE.comp
          (AlgebraicKTheory.StableSteinberg.lastRowProduct n)) r =
          rowStableHom (R := R) n r := by rw [h]
      simpa [MonoidHom.comp_apply] using h1
    calc AlgebraicKTheory.StableSteinberg.toStableE
          (AlgebraicKTheory.StableSteinberg.lastBoundaryBlock (R := R) n
            (Sum.inr r))
        = AlgebraicKTheory.StableSteinberg.toStableE
            (AlgebraicKTheory.StableSteinberg.lastRowProduct n r) := by
          rw [h_row]
      _ = rowStableHom (R := R) n r := h_toRow
      _ = AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
            (rowSubgroupHom n r) := rfl
      _ = AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
            (lastBoundaryBlockElementary n (Sum.inr r)) := rfl

/-- Evaluation of a word of last-boundary blocks via `toStableE` equals the
stable elementary evaluation of the corresponding finite `n+1` elementary word.

Finite rank `n+1`, generic ring `R` (universe `u`), arbitrary word length,
both block orientations preserved pointwise. Proved by transparent list
induction using `toStableE_lastBoundaryBlock` and homomorphism laws
`map_mul` / `map_prod`.

Proves evaluation only; makes no pivot, scalar-equation, alternation,
kernel-generation, finite-stage landing, strict-decrease, cocycle,
naturality, or Matsumoto claim. -/
public theorem toStableE_lastBoundaryBlock_list_prod (n : ℕ)
    (L : List (Sum (Fin n → Multiplicative R)
      (Fin n → Multiplicative R))) :
    AlgebraicKTheory.StableSteinberg.toStableE
        ((L.map (AlgebraicKTheory.StableSteinberg.lastBoundaryBlock n)).prod) =
      AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
        ((L.map (lastBoundaryBlockElementary n)).prod) := by
  induction L with
  | nil =>
    simp [map_one]
  | cons b rest ih =>
    simp only [List.map_cons, List.prod_cons]
    calc AlgebraicKTheory.StableSteinberg.toStableE
          (AlgebraicKTheory.StableSteinberg.lastBoundaryBlock n b *
            (List.map (AlgebraicKTheory.StableSteinberg.lastBoundaryBlock n)
              rest).prod)
        = AlgebraicKTheory.StableSteinberg.toStableE
            (AlgebraicKTheory.StableSteinberg.lastBoundaryBlock n b) *
          AlgebraicKTheory.StableSteinberg.toStableE
            ((List.map (AlgebraicKTheory.StableSteinberg.lastBoundaryBlock n)
              rest).prod) := by rw [map_mul]
      _ = AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
            (lastBoundaryBlockElementary n b) *
          AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
            ((List.map (lastBoundaryBlockElementary n) rest).prod) := by
          rw [toStableE_lastBoundaryBlock, ih]
      _ = AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
            (lastBoundaryBlockElementary n b *
              (List.map (lastBoundaryBlockElementary n) rest).prod) := by
          rw [← map_mul]
      _ = AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
            ((List.map (lastBoundaryBlockElementary n) (b :: rest)).prod) := by
          simp

/-- If the stable evaluation of a last-boundary-block word is trivial then its
finite `n+1` elementary representative word is trivial.

Finite rank `n+1`, generic ring `R` (universe `u`). Deduction uses
`toStableE_lastBoundaryBlock_list_prod`, `map_one`, and
`StableE.fromFinite_injective`; no additional algebraic hypothesis.

Proves evaluation only; makes no pivot, scalar-equation, alternation,
kernel-generation, finite-stage landing, strict-decrease, cocycle,
naturality, or Matsumoto claim. -/
public theorem toStableE_lastBoundaryBlock_list_prod_eq_one_imp (n : ℕ)
    (L : List (Sum (Fin n → Multiplicative R)
      (Fin n → Multiplicative R)))
    (h : AlgebraicKTheory.StableSteinberg.toStableE
        ((L.map (AlgebraicKTheory.StableSteinberg.lastBoundaryBlock n)).prod) =
      1) :
    ((L.map (lastBoundaryBlockElementary (R := R) n)).prod :
      Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) R) = 1 := by
  have h_prod := toStableE_lastBoundaryBlock_list_prod (R := R) n L
  have h_from :
      AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
          ((L.map (lastBoundaryBlockElementary n)).prod) = 1 := by
    calc AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
          ((L.map (lastBoundaryBlockElementary n)).prod)
        = AlgebraicKTheory.StableSteinberg.toStableE
            ((L.map (AlgebraicKTheory.StableSteinberg.lastBoundaryBlock n)).prod) :=
          h_prod.symm
      _ = 1 := h
  have h_one :
      AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
          ((L.map (lastBoundaryBlockElementary n)).prod) =
        AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1) 1 := by
    rw [h_from, map_one]
  exact AlgebraicKTheory.StableE.fromFinite_injective (R := R) (n + 1) h_one

/-- Finite elementary product equals reindexed alternating block product.

Direction is from the finite elementary representatives
`lastBoundaryBlockElementary n` (in `elementarySubgroup (Fin (n+1))`)
to the explicit `GL (Fin n ⊕ Fin 1)` alternating product
`BlockElementary.blockAltProd` reindexed by `finSumFinEquiv`.

Orientation is exact: `Sum.inl c` is column = upper unit
`BlockElementary.upperUnit` with `Matrix.of fun i _ => (c i).toAdd`, and
`Sum.inr r` is row = lower unit `BlockElementary.lowerUnit` with
`Matrix.of fun _ j => (r j).toAdd`.

Generic `[Ring R]` and universe `u`, arbitrary length `L`, empty list gives
`1` via `blockAltProd_nil` and `List.prod` on `[]`, singleton reduces to
`lastBoundaryBlockElementary_inl_val` / `_inr_val`, and `n = 0` is valid
(`Fin 0 → _` is subsingleton, `Fin 1` block is trivial). Multiplication order
preserves head-left `List.prod` (`a :: L` multiplies on the left). This is a
representation/evaluation bridge only; no pivot, scalar equation, alternation,
strict decrease, kernel generation, finite-stage landing, or Matsumoto claim
is made. -/
public theorem lastBoundaryBlockElementary_list_prod_val
    (n : ℕ)
    (L : List (Sum (Fin n → Multiplicative R)
      (Fin n → Multiplicative R))) :
    (↑((L.map (lastBoundaryBlockElementary (R := R) n)).prod) :
      Matrix.GeneralLinearGroup (Fin (n + 1)) R) =
    Matrix.GeneralLinearGroup.reindexMulEquiv
      (finSumFinEquiv (m := n) (n := 1))
      (Matrix.GeneralLinearGroup.BlockElementary.blockAltProd
        (L.map (Sum.elim
          (fun c : Fin n → Multiplicative R =>
            Sum.inl (Matrix.of fun (i : Fin n) (_ : Fin 1) => (c i).toAdd))
          (fun r : Fin n → Multiplicative R =>
            Sum.inr (Matrix.of fun (_ : Fin 1) (j : Fin n) => (r j).toAdd))))) := by
  change (↑((L.map (lastBoundaryBlockElementary (R := R) n)).prod) :
      Matrix.GeneralLinearGroup (Fin (n + 1)) R) =
    Matrix.GeneralLinearGroup.reindexMulEquiv (finSumFinEquiv (m := n) (n := 1))
      (Matrix.GeneralLinearGroup.BlockElementary.blockAltProd
        (L.map (coeffToBlock (R := R) n)))
  induction L with
  | nil =>
    simp [Matrix.GeneralLinearGroup.BlockElementary.blockAltProd_nil]
  | cons hd tl ih =>
    have h_hd : (↑(lastBoundaryBlockElementary (R := R) n hd) :
        Matrix.GeneralLinearGroup (Fin (n + 1)) R) =
        Matrix.GeneralLinearGroup.reindexMulEquiv
          (finSumFinEquiv (m := n) (n := 1))
          (Sum.elim Matrix.GeneralLinearGroup.BlockElementary.upperUnit
            Matrix.GeneralLinearGroup.BlockElementary.lowerUnit
            (coeffToBlock (R := R) n hd)) :=
      lastBoundaryBlockElementary_val (R := R) n hd
    have h_prod_eq : (List.map (lastBoundaryBlockElementary (R := R) n)
          (hd :: tl)).prod =
        lastBoundaryBlockElementary (R := R) n hd *
        (List.map (lastBoundaryBlockElementary (R := R) n) tl).prod := by
      simp [List.map_cons, List.prod_cons]
    calc (↑((List.map (lastBoundaryBlockElementary (R := R) n)
            (hd :: tl)).prod) : Matrix.GeneralLinearGroup (Fin (n + 1)) R)
        = ↑(lastBoundaryBlockElementary (R := R) n hd *
          (List.map (lastBoundaryBlockElementary (R := R) n) tl).prod) :=
        congrArg Subtype.val h_prod_eq
      _ = (↑(lastBoundaryBlockElementary (R := R) n hd) :
            Matrix.GeneralLinearGroup (Fin (n + 1)) R) *
          (↑((List.map (lastBoundaryBlockElementary (R := R) n) tl).prod) :
            Matrix.GeneralLinearGroup (Fin (n + 1)) R) := rfl
      _ = Matrix.GeneralLinearGroup.reindexMulEquiv
            (finSumFinEquiv (m := n) (n := 1))
            (Sum.elim Matrix.GeneralLinearGroup.BlockElementary.upperUnit
              Matrix.GeneralLinearGroup.BlockElementary.lowerUnit
              (coeffToBlock (R := R) n hd)) *
          Matrix.GeneralLinearGroup.reindexMulEquiv
            (finSumFinEquiv (m := n) (n := 1))
            (Matrix.GeneralLinearGroup.BlockElementary.blockAltProd
              (List.map (coeffToBlock (R := R) n) tl)) := by
        rw [h_hd, ih]
      _ = Matrix.GeneralLinearGroup.reindexMulEquiv
            (finSumFinEquiv (m := n) (n := 1))
            (Sum.elim Matrix.GeneralLinearGroup.BlockElementary.upperUnit
              Matrix.GeneralLinearGroup.BlockElementary.lowerUnit
              (coeffToBlock (R := R) n hd) *
            Matrix.GeneralLinearGroup.BlockElementary.blockAltProd
              (List.map (coeffToBlock (R := R) n) tl)) := by
        rw [← MulEquiv.map_mul]
      _ = Matrix.GeneralLinearGroup.reindexMulEquiv
            (finSumFinEquiv (m := n) (n := 1))
            (Matrix.GeneralLinearGroup.BlockElementary.blockAltProd
              (List.map (coeffToBlock (R := R) n) (hd :: tl))) := by
        have h_block : Matrix.GeneralLinearGroup.BlockElementary.blockAltProd
              (List.map (coeffToBlock (R := R) n) (hd :: tl)) =
            Sum.elim Matrix.GeneralLinearGroup.BlockElementary.upperUnit
              Matrix.GeneralLinearGroup.BlockElementary.lowerUnit
              (coeffToBlock (R := R) n hd) *
            Matrix.GeneralLinearGroup.BlockElementary.blockAltProd
              (List.map (coeffToBlock (R := R) n) tl) := by
          simp [Matrix.GeneralLinearGroup.BlockElementary.blockAltProd]
        rw [← h_block]

/-- From a stable-trivial boundary word to a trivial alternating block product.

If the `toStableE`-image of the `lastBoundaryBlock n` word
`(L.map lastBoundaryBlock n).prod` is `1` in `StableE`, then the explicit
alternating block product in `GL (Fin n ⊕ Fin 1)` is `1`.

Direction uses the finite elementary-product equality
`toStableE_lastBoundaryBlock_list_prod_eq_one_imp` to obtain
`((L.map lastBoundaryBlockElementary n).prod : elementarySubgroup) = 1`,
coerces to `GL (Fin (n+1))`, rewrites via
`lastBoundaryBlockElementary_list_prod_val`, and applies injectivity of
`reindexMulEquiv (finSumFinEquiv)`.

Orientation is exact: `Sum.inl` is column = upper unit with
`Matrix.of fun i _ => (c i).toAdd`, `Sum.inr` is row = lower unit with
`Matrix.of fun _ j => (r j).toAdd`.

Generic `[Ring R]` and universe `u`, arbitrary `L`, empty `L` gives `1` on
both sides, singleton reduces to the single-block evaluation, and `n = 0`
is valid (`Fin 0` vectors are trivial). This is a representation/evaluation
bridge only; no pivot, scalar equation, alternation, strict decrease, kernel
generation, finite-stage landing, Weyl stage drop, torus-cocycle, or
Matsumoto claim is made. -/
public theorem
    toStableE_lastBoundaryBlock_list_prod_eq_one_imp_blockAltProd_eq_one
    (n : ℕ)
    (L : List (Sum (Fin n → Multiplicative R)
      (Fin n → Multiplicative R)))
    (h : AlgebraicKTheory.StableSteinberg.toStableE
        ((L.map (AlgebraicKTheory.StableSteinberg.lastBoundaryBlock
          (R := R) n)).prod) = 1) :
    Matrix.GeneralLinearGroup.BlockElementary.blockAltProd
      (L.map (Sum.elim
        (fun c : Fin n → Multiplicative R =>
          Sum.inl (Matrix.of fun (i : Fin n) (_ : Fin 1) => (c i).toAdd))
        (fun r : Fin n → Multiplicative R =>
          Sum.inr (Matrix.of fun (_ : Fin 1) (j : Fin n) => (r j).toAdd)))) = 1 := by
  have h_elem :
      ((L.map (lastBoundaryBlockElementary (R := R) n)).prod :
        Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) R) = 1 :=
    toStableE_lastBoundaryBlock_list_prod_eq_one_imp (R := R) n L h
  have h_coe :
      (↑((L.map (lastBoundaryBlockElementary (R := R) n)).prod) :
        Matrix.GeneralLinearGroup (Fin (n + 1)) R) = 1 := by
    calc (↑((L.map (lastBoundaryBlockElementary (R := R) n)).prod) :
          Matrix.GeneralLinearGroup (Fin (n + 1)) R)
        = ↑(1 : Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) R) :=
          congrArg Subtype.val h_elem
      _ = 1 := rfl
  have h_reindex :
      Matrix.GeneralLinearGroup.reindexMulEquiv
          (finSumFinEquiv (m := n) (n := 1))
          (Matrix.GeneralLinearGroup.BlockElementary.blockAltProd
            (L.map (Sum.elim
              (fun c : Fin n → Multiplicative R =>
                Sum.inl (Matrix.of fun (i : Fin n) (_ : Fin 1) => (c i).toAdd))
              (fun r : Fin n → Multiplicative R =>
                Sum.inr
                  (Matrix.of fun (_ : Fin 1) (j : Fin n) => (r j).toAdd))))) =
        1 := by
    calc Matrix.GeneralLinearGroup.reindexMulEquiv
            (finSumFinEquiv (m := n) (n := 1))
            (Matrix.GeneralLinearGroup.BlockElementary.blockAltProd
              (L.map (Sum.elim
                (fun c : Fin n → Multiplicative R =>
                  Sum.inl (Matrix.of fun (i : Fin n) (_ : Fin 1) => (c i).toAdd))
                (fun r : Fin n → Multiplicative R =>
                  Sum.inr
                    (Matrix.of fun (_ : Fin 1) (j : Fin n) => (r j).toAdd)))))
        = (↑((L.map (lastBoundaryBlockElementary (R := R) n)).prod) :
            Matrix.GeneralLinearGroup (Fin (n + 1)) R) := by
          rw [← lastBoundaryBlockElementary_list_prod_val (R := R) n L]
      _ = 1 := h_coe
  exact (MulEquiv.injective
    (Matrix.GeneralLinearGroup.reindexMulEquiv
      (finSumFinEquiv (m := n) (n := 1))))
    (by rw [h_reindex, MulEquiv.map_one])

end StableSteinberg
end AlgebraicKTheory
