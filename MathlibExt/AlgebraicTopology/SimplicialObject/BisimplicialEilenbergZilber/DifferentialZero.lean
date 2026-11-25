/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.DifferentialPositive

/-!
# Zero-boundary cases for the bisimplicial shuffle differential

When one bidegree is zero, every shuffle boundary face lies in the other
direction.  This file proves the two corresponding edge identities directly
from the existing left- and right-boundary shuffle bijections and sign
formulas.  Together with the positive-bidegree theorem, these cover every
bidegree of the total complex.
-/

@[expose] public section

open CategoryTheory Simplicial SimplexCategory
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialEilenbergZilber

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [Category.{v} A] [Preadditive A]
  (B : SimplicialObject (SimplicialObject A))

noncomputable def diagonalBoundaryMapRightZero (p : ℕ)
    (s : AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) 0)
    (i : Fin ((p + 1) + 0 + 1)) :
    (B.obj (Opposite.op ⦋p + 1⦌)).obj (Opposite.op ⦋0⦌) ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X p :=
  shuffleMap B s ≫
    ((SimplicialObject.diagonalFunctor A).obj B).δ
      (n := p) (Fin.cast (by omega) i)

theorem diagonalBoundaryMapRightZero_eq_map (p : ℕ)
    (s : AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) 0)
    (i : Fin ((p + 1) + 0 + 1)) :
    diagonalBoundaryMapRightZero B p s i =
      AlgebraicTopology.Bisimplicial.map B
        (SimplexCategory.δ (n := p) (Fin.cast (by omega) i) ≫ s.leftHom)
        (SimplexCategory.δ (n := p) (Fin.cast (by omega) i) ≫ s.rightHom) := by
  unfold diagonalBoundaryMapRightZero shuffleMap
  change AlgebraicTopology.Bisimplicial.map B s.leftHom s.rightHom ≫
      ((SimplicialObject.diagonalFunctor A).obj B).map
        (SimplexCategory.δ (n := p) (Fin.cast (by omega) i)).op = _
  rw [← AlgebraicTopology.Bisimplicial.map_diagonal]
  exact AlgebraicTopology.Bisimplicial.map_comp _ _ _ _ _

noncomputable def shuffleBoundaryTermRightZero (p : ℕ)
    (s : AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) 0)
    (i : Fin ((p + 1) + 0 + 1)) :
    (B.obj (Opposite.op ⦋p + 1⦌)).obj (Opposite.op ⦋0⦌) ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X p :=
  ((-1 : ℤ) ^ i.val) • diagonalBoundaryMapRightZero B p s i

private theorem leftBoundaryIndex_succAbove_castZero {p q : ℕ}
    (t : AlgebraicTopology.EilenbergZilber.Shuffle p q)
    (a : Fin (p + 2)) (k : Fin (p + q + 1)) :
    Fin.cast (by omega) ((Fin.cast (by omega)
      (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryIndex t a)).succAbove k) =
      (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryIndex t a).succAbove
        (Fin.cast (by omega) k) := by
  apply Fin.ext
  simp only [Fin.succAbove, Fin.val_cast, Fin.val_castSucc, Fin.val_succ,
    apply_ite Fin.val]
  split_ifs
  all_goals simp_all [Fin.lt_def]
  omega

private theorem leftBoundaryShuffle_leftHom_eq_raw {p q : ℕ}
    (t : AlgebraicTopology.EilenbergZilber.Shuffle p q)
    (a : Fin (p + 2)) :
    SimplexCategory.δ
          (Fin.cast (by omega)
            (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryIndex t a)) ≫
      eqToHom (by rw [show p + q + 1 = (p + 1) + q by omega]) ≫
        (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryShuffle t a).leftHom =
      t.leftHom ≫ SimplexCategory.δ a := by
  ext k
  change Fin (p + q + 1) at k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
    OrderHom.comp_coe, Function.comp_apply, OrderEmbedding.toOrderHom_coe,
    OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
    Fin.succAboveOrderEmb_apply]
  rw [leftBoundaryIndex_succAbove_castZero]
  exact congrArg Fin.val
    (AlgebraicTopology.EilenbergZilber.Shuffle.leftHom_leftBoundaryShuffle_succAbove
      t a k)

private theorem leftBoundaryShuffle_rightHom_eq_raw {p q : ℕ}
    (t : AlgebraicTopology.EilenbergZilber.Shuffle p q)
    (a : Fin (p + 2)) :
    SimplexCategory.δ
          (Fin.cast (by omega)
            (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryIndex t a)) ≫
      eqToHom (by rw [show p + q + 1 = (p + 1) + q by omega]) ≫
        (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryShuffle t a).rightHom =
      t.rightHom := by
  ext k
  change Fin (p + q + 1) at k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
    OrderHom.comp_coe, Function.comp_apply, OrderEmbedding.toOrderHom_coe,
    OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
    Fin.succAboveOrderEmb_apply]
  rw [leftBoundaryIndex_succAbove_castZero]
  exact congrArg Fin.val
    (AlgebraicTopology.EilenbergZilber.Shuffle.rightHom_leftBoundaryShuffle_succAbove
      t a k)

private theorem leftBoundaryZero_outerHom_eq {p : ℕ}
    (t : AlgebraicTopology.EilenbergZilber.Shuffle p 0)
    (a : Fin (p + 2)) :
    SimplexCategory.δ (n := p)
          (Fin.cast (by omega)
            (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryIndex t a)) ≫
        (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryShuffle t a).leftHom =
      t.leftHom ≫ SimplexCategory.δ a := by
  simpa using leftBoundaryShuffle_leftHom_eq_raw t a

private theorem leftBoundaryZero_innerHom_eq {p : ℕ}
    (t : AlgebraicTopology.EilenbergZilber.Shuffle p 0)
    (a : Fin (p + 2)) :
    SimplexCategory.δ (n := p)
          (Fin.cast (by omega)
            (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryIndex t a)) ≫
        (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryShuffle t a).rightHom =
      t.rightHom := by
  simpa using leftBoundaryShuffle_rightHom_eq_raw t a

theorem diagonalBoundaryMapRightZero_leftBoundary (p : ℕ)
    (t : AlgebraicTopology.EilenbergZilber.Shuffle p 0)
    (a : Fin (p + 2)) :
    diagonalBoundaryMapRightZero B p
        (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryShuffle t a)
        (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryIndex t a) =
      (B.δ a).app (Opposite.op ⦋0⦌) ≫ shuffleMap B t := by
  rw [diagonalBoundaryMapRightZero_eq_map]
  unfold shuffleMap
  rw [← AlgebraicTopology.Bisimplicial.map_delta_id]
  rw [AlgebraicTopology.Bisimplicial.map_comp]
  simp only [Category.comp_id]
  exact congrArg₂ (AlgebraicTopology.Bisimplicial.map B)
    (leftBoundaryZero_outerHom_eq t a) (leftBoundaryZero_innerHom_eq t a)

theorem shuffleBoundaryTermRightZero_leftBoundary (p : ℕ)
    (t : AlgebraicTopology.EilenbergZilber.Shuffle p 0)
    (a : Fin (p + 2)) :
    AlgebraicTopology.EilenbergZilber.shuffleSignZ
          (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryShuffle t a) •
        shuffleBoundaryTermRightZero B p
          (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryShuffle t a)
          (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryIndex t a) =
      ((-1 : ℤ) ^ a.val) •
        ((B.δ a).app (Opposite.op ⦋0⦌) ≫ shuffleSummand B t) := by
  unfold shuffleBoundaryTermRightZero shuffleSummand
  rw [diagonalBoundaryMapRightZero_leftBoundary]
  simp only [Preadditive.comp_zsmul, smul_smul]
  rw [mul_comm]
  rw [AlgebraicTopology.EilenbergZilber.Shuffle.shuffleSignZ_leftBoundaryShuffle]

private theorem shuffleBidegree_comp_objD_eq_boundary_sum_right_zero (p : ℕ) :
    shuffleBidegree B (p + 1) 0 ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD
          ((SimplicialObject.diagonalFunctor A).obj B) p =
      ∑ z : AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) 0 ×
          Fin ((p + 1) + 0 + 1),
        ((-1 : ℤ) ^ z.2.val) •
          (shuffleSummand B z.1 ≫
            ((SimplicialObject.diagonalFunctor A).obj B).δ
              (n := p) (Fin.cast (by omega) z.2)) := by
  unfold shuffleBidegree AlgebraicTopology.AlternatingFaceMapComplex.objD
  simp only [Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.comp_zsmul, Finset.smul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_product']
  apply Finset.sum_congr rfl
  intro z _
  rfl

private theorem shuffleBidegree_comp_objD_eq_signed_boundary_sum_right_zero
    (p : ℕ) :
    shuffleBidegree B (p + 1) 0 ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD
          ((SimplicialObject.diagonalFunctor A).obj B) p =
      ∑ z : AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) 0 ×
          Fin ((p + 1) + 0 + 1),
        AlgebraicTopology.EilenbergZilber.shuffleSignZ z.1 •
          shuffleBoundaryTermRightZero B p z.1 z.2 := by
  rw [shuffleBidegree_comp_objD_eq_boundary_sum_right_zero]
  apply Finset.sum_congr rfl
  intro z _
  simp only [shuffleBoundaryTermRightZero, diagonalBoundaryMapRightZero,
    shuffleSummand, Preadditive.zsmul_comp, smul_smul]
  congr 1
  ring

private theorem shuffleBidegree_comp_objD_eq_left_boundary_sum_right_zero
    (p : ℕ) :
    shuffleBidegree B (p + 1) 0 ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD
          ((SimplicialObject.diagonalFunctor A).obj B) p =
      ∑ x : Fin (p + 2) × AlgebraicTopology.EilenbergZilber.Shuffle p 0,
        AlgebraicTopology.EilenbergZilber.shuffleSignZ
            (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryPair x).1 •
          shuffleBoundaryTermRightZero B p
            (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryPair x).1
            (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryPair x).2 := by
  rw [shuffleBidegree_comp_objD_eq_signed_boundary_sum_right_zero]
  have hnonmixed :
      AlgebraicTopology.EilenbergZilber.Shuffle.nonmixedBoundaryFaces (p + 1) 0 =
        Finset.univ := by
    ext z
    simp only [AlgebraicTopology.EilenbergZilber.Shuffle.nonmixedBoundaryFaces,
      Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact AlgebraicTopology.EilenbergZilber.Shuffle.isLeftBoundary_not_isMixedBoundary
      (AlgebraicTopology.EilenbergZilber.Shuffle.isLeftBoundary_of_right_zero z.1 z.2)
  have h := AlgebraicTopology.EilenbergZilber.Shuffle.sum_nonmixedBoundaryFaces_right_zero
    (fun s i => AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
      shuffleBoundaryTermRightZero B p s i)
  simpa only [hnonmixed, Finset.sum_filter, Finset.sum_const_zero, add_zero] using h

theorem shuffleBidegree_comp_objD_right_zero (p : ℕ) :
    shuffleBidegree B (p + 1) 0 ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD
          ((SimplicialObject.diagonalFunctor A).obj B) p =
      (AlgebraicTopology.AlternatingFaceMapComplex.objD B p).app
          (Opposite.op ⦋0⦌) ≫ shuffleBidegree B p 0 := by
  rw [shuffleBidegree_comp_objD_eq_left_boundary_sum_right_zero]
  rw [Fintype.sum_prod_type]
  simp_rw [AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryPair,
    shuffleBoundaryTermRightZero_leftBoundary]
  unfold AlgebraicTopology.AlternatingFaceMapComplex.objD shuffleBidegree
  simp only [NatTrans.app_sum, NatTrans.app_zsmul,
    Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.zsmul_comp]
  rw [Finset.sum_comm]

noncomputable def diagonalBoundaryMapLeftZero (q : ℕ)
    (s : AlgebraicTopology.EilenbergZilber.Shuffle 0 (q + 1))
    (i : Fin (0 + (q + 1) + 1)) :
    (B.obj (Opposite.op ⦋0⦌)).obj (Opposite.op ⦋q + 1⦌) ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
        (0 + q) :=
  shuffleMap B s ≫
    ((SimplicialObject.diagonalFunctor A).obj B).δ
      (n := 0 + q) (Fin.cast (by omega) i)

theorem diagonalBoundaryMapLeftZero_eq_map (q : ℕ)
    (s : AlgebraicTopology.EilenbergZilber.Shuffle 0 (q + 1))
    (i : Fin (0 + (q + 1) + 1)) :
    diagonalBoundaryMapLeftZero B q s i =
      AlgebraicTopology.Bisimplicial.map B
        (SimplexCategory.δ (n := 0 + q) (Fin.cast (by omega) i) ≫ s.leftHom)
        (SimplexCategory.δ (n := 0 + q) (Fin.cast (by omega) i) ≫ s.rightHom) := by
  unfold diagonalBoundaryMapLeftZero shuffleMap
  change AlgebraicTopology.Bisimplicial.map B s.leftHom s.rightHom ≫
      ((SimplicialObject.diagonalFunctor A).obj B).map
        (SimplexCategory.δ (n := 0 + q) (Fin.cast (by omega) i)).op = _
  rw [← AlgebraicTopology.Bisimplicial.map_diagonal]
  exact AlgebraicTopology.Bisimplicial.map_comp _ _ _ _ _

noncomputable def shuffleBoundaryTermLeftZero (q : ℕ)
    (s : AlgebraicTopology.EilenbergZilber.Shuffle 0 (q + 1))
    (i : Fin (0 + (q + 1) + 1)) :
    (B.obj (Opposite.op ⦋0⦌)).obj (Opposite.op ⦋q + 1⦌) ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
        (0 + q) :=
  ((-1 : ℤ) ^ i.val) • diagonalBoundaryMapLeftZero B q s i

private theorem rightBoundaryIndex_succAbove_castZero {p q : ℕ}
    (t : AlgebraicTopology.EilenbergZilber.Shuffle p q)
    (b : Fin (q + 2)) (k : Fin (p + q + 1)) :
    (Fin.cast rfl
      (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryIndex t b)).succAbove k =
      (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryIndex t b).succAbove
        (Fin.cast (by omega) k) := by
  apply Fin.ext
  simp only [Fin.succAbove, Fin.val_cast, Fin.val_castSucc, Fin.val_succ,
    apply_ite Fin.val]
  split_ifs
  all_goals simp_all [Fin.lt_def]
  omega

private theorem rightBoundaryShuffle_rightHom_eq_raw {p q : ℕ}
    (t : AlgebraicTopology.EilenbergZilber.Shuffle p q)
    (b : Fin (q + 2)) :
    SimplexCategory.δ
          (Fin.cast rfl
            (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryIndex
              (p := p) (q := q) t b)) ≫
        (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryShuffle
          (p := p) (q := q) t b).rightHom =
      t.rightHom ≫ SimplexCategory.δ b := by
  ext k
  change Fin (p + q + 1) at k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    SimplexCategory.len_mk, OrderHom.comp_coe, Function.comp_apply,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [rightBoundaryIndex_succAbove_castZero]
  exact congrArg Fin.val
    (AlgebraicTopology.EilenbergZilber.Shuffle.rightHom_rightBoundaryShuffle_succAbove
      t b k)

private theorem rightBoundaryShuffle_leftHom_eq_raw {p q : ℕ}
    (t : AlgebraicTopology.EilenbergZilber.Shuffle p q)
    (b : Fin (q + 2)) :
    SimplexCategory.δ
          (Fin.cast rfl
            (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryIndex
              (p := p) (q := q) t b)) ≫
        (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryShuffle
          (p := p) (q := q) t b).leftHom =
      t.leftHom := by
  ext k
  change Fin (p + q + 1) at k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    SimplexCategory.len_mk, OrderHom.comp_coe, Function.comp_apply,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [rightBoundaryIndex_succAbove_castZero]
  exact congrArg Fin.val
    (AlgebraicTopology.EilenbergZilber.Shuffle.leftHom_rightBoundaryShuffle_succAbove
      t b k)

theorem diagonalBoundaryMapLeftZero_rightBoundary (q : ℕ)
    (t : AlgebraicTopology.EilenbergZilber.Shuffle 0 q)
    (b : Fin (q + 2)) :
    diagonalBoundaryMapLeftZero B q
        (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryShuffle t b)
        (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryIndex t b) =
      (B.obj (Opposite.op ⦋0⦌)).δ b ≫ shuffleMap B t := by
  rw [diagonalBoundaryMapLeftZero_eq_map]
  unfold shuffleMap
  rw [← AlgebraicTopology.Bisimplicial.map_id_delta]
  rw [AlgebraicTopology.Bisimplicial.map_comp]
  simp only [Category.comp_id]
  exact congrArg₂ (AlgebraicTopology.Bisimplicial.map B)
    (rightBoundaryShuffle_leftHom_eq_raw t b)
    (rightBoundaryShuffle_rightHom_eq_raw t b)

theorem shuffleBoundaryTermLeftZero_rightBoundary (q : ℕ)
    (t : AlgebraicTopology.EilenbergZilber.Shuffle 0 q)
    (b : Fin (q + 2)) :
    AlgebraicTopology.EilenbergZilber.shuffleSignZ
          (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryShuffle t b) •
        shuffleBoundaryTermLeftZero B q
          (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryShuffle t b)
          (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryIndex t b) =
      ((-1 : ℤ) ^ b.val) •
        ((B.obj (Opposite.op ⦋0⦌)).δ b ≫ shuffleSummand B t) := by
  unfold shuffleBoundaryTermLeftZero shuffleSummand
  rw [diagonalBoundaryMapLeftZero_rightBoundary]
  simp only [Preadditive.comp_zsmul, smul_smul]
  rw [mul_comm]
  rw [AlgebraicTopology.EilenbergZilber.Shuffle.shuffleSignZ_rightBoundaryShuffle]
  simp only [zero_add]

private theorem shuffleBidegree_comp_objD_eq_boundary_sum_left_zero (q : ℕ) :
    shuffleBidegree B 0 (q + 1) ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD
          ((SimplicialObject.diagonalFunctor A).obj B) (0 + q) =
      ∑ z : AlgebraicTopology.EilenbergZilber.Shuffle 0 (q + 1) ×
          Fin (0 + (q + 1) + 1),
        ((-1 : ℤ) ^ z.2.val) •
          (shuffleSummand B z.1 ≫
            ((SimplicialObject.diagonalFunctor A).obj B).δ
              (n := 0 + q) (Fin.cast (by omega) z.2)) := by
  unfold shuffleBidegree AlgebraicTopology.AlternatingFaceMapComplex.objD
  simp only [Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.comp_zsmul, Finset.smul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_product']
  apply Finset.sum_congr rfl
  intro z _
  rfl

private theorem shuffleBidegree_comp_objD_eq_signed_boundary_sum_left_zero
    (q : ℕ) :
    shuffleBidegree B 0 (q + 1) ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD
          ((SimplicialObject.diagonalFunctor A).obj B) (0 + q) =
      ∑ z : AlgebraicTopology.EilenbergZilber.Shuffle 0 (q + 1) ×
          Fin (0 + (q + 1) + 1),
        AlgebraicTopology.EilenbergZilber.shuffleSignZ z.1 •
          shuffleBoundaryTermLeftZero B q z.1 z.2 := by
  rw [shuffleBidegree_comp_objD_eq_boundary_sum_left_zero]
  apply Finset.sum_congr rfl
  intro z _
  simp only [shuffleBoundaryTermLeftZero, diagonalBoundaryMapLeftZero,
    shuffleSummand, Preadditive.zsmul_comp, smul_smul]
  congr 1
  ring

private theorem shuffleBidegree_comp_objD_eq_right_boundary_sum_left_zero
    (q : ℕ) :
    shuffleBidegree B 0 (q + 1) ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD
          ((SimplicialObject.diagonalFunctor A).obj B) (0 + q) =
      ∑ x : Fin (q + 2) × AlgebraicTopology.EilenbergZilber.Shuffle 0 q,
        AlgebraicTopology.EilenbergZilber.shuffleSignZ
            (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryPair x).1 •
          shuffleBoundaryTermLeftZero B q
            (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryPair x).1
            (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryPair x).2 := by
  rw [shuffleBidegree_comp_objD_eq_signed_boundary_sum_left_zero]
  have hnonmixed :
      AlgebraicTopology.EilenbergZilber.Shuffle.nonmixedBoundaryFaces 0 (q + 1) =
        Finset.univ := by
    ext z
    simp only [AlgebraicTopology.EilenbergZilber.Shuffle.nonmixedBoundaryFaces,
      Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact AlgebraicTopology.EilenbergZilber.Shuffle.isRightBoundary_not_isMixedBoundary
      (AlgebraicTopology.EilenbergZilber.Shuffle.isRightBoundary_of_left_zero z.1 z.2)
  have h := AlgebraicTopology.EilenbergZilber.Shuffle.sum_nonmixedBoundaryFaces_left_zero
    (fun s i => AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
      shuffleBoundaryTermLeftZero B q s i)
  simpa only [hnonmixed, Finset.sum_filter, Finset.sum_const_zero, add_zero] using h

theorem shuffleBidegree_comp_objD_left_zero (q : ℕ) :
    shuffleBidegree B 0 (q + 1) ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD
          ((SimplicialObject.diagonalFunctor A).obj B) (0 + q) =
      AlgebraicTopology.AlternatingFaceMapComplex.objD
          (B.obj (Opposite.op ⦋0⦌)) q ≫ shuffleBidegree B 0 q := by
  rw [shuffleBidegree_comp_objD_eq_right_boundary_sum_left_zero]
  rw [Fintype.sum_prod_type]
  simp_rw [AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryPair,
    shuffleBoundaryTermLeftZero_rightBoundary]
  unfold AlgebraicTopology.AlternatingFaceMapComplex.objD shuffleBidegree
  simp only [Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.zsmul_comp]
  rw [Finset.sum_comm]

end AlgebraicTopology.BisimplicialEilenbergZilber
