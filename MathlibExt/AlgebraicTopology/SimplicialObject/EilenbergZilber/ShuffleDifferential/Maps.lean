/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryDecomposition
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryLeft.Maps
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryRight.Maps

@[expose] public section

namespace AlgebraicTopology.EilenbergZilber

open CategoryTheory Simplicial SimplexCategory

open scoped BigOperators MonoidalCategory

private theorem leftBoundaryIndex_succAbove_cast {p q : ℕ} (t : Shuffle p q)
    (a : Fin (p + 2)) (k : Fin (p + q + 1)) :
    Fin.cast (by omega) ((Fin.cast (by omega)
      (Shuffle.leftBoundaryIndex (p := p) (q := q) t a)).succAbove k) =
      (Shuffle.leftBoundaryIndex (p := p) (q := q) t a).succAbove
        (Fin.cast (by omega) k) := by
  apply Fin.ext
  simp only [Fin.succAbove, Fin.val_cast, Fin.val_castSucc, Fin.val_succ, apply_ite Fin.val]
  split_ifs
  all_goals simp_all [Fin.lt_def]
  omega

private theorem leftBoundaryShuffle_leftHom_eq {p q : ℕ} (t : Shuffle p q)
    (a : Fin (p + 2)) :
    SimplexCategory.δ (Fin.cast (by omega) (Shuffle.leftBoundaryIndex (p := p) (q := q) t a)) ≫
      eqToHom (by rw [show p + q + 1 = (p + 1) + q by omega]) ≫
        (Shuffle.leftBoundaryShuffle (p := p) (q := q) t a).leftHom =
      t.leftHom ≫ SimplexCategory.δ a := by
  ext k
  change Fin (p + q + 1) at k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
    OrderHom.comp_coe, Function.comp_apply, OrderEmbedding.toOrderHom_coe,
    OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply, Fin.succAboveOrderEmb_apply]
  rw [leftBoundaryIndex_succAbove_cast]
  exact congrArg Fin.val (Shuffle.leftHom_leftBoundaryShuffle_succAbove t a k)

theorem leftBoundaryShuffle_left_map {C : Type*} [CategoryTheory.Category C]
    (X : SimplicialObject C) {p q : ℕ} (t : Shuffle p q) (a : Fin (p + 2)) :
    X.map (Shuffle.leftBoundaryShuffle (p := p) (q := q) t a).leftHom.op ≫
      eqToHom (by rw [show (p + 1) + q = p + q + 1 by omega]) ≫
      X.δ (Fin.cast (by omega) (Shuffle.leftBoundaryIndex (p := p) (q := q) t a)) =
      X.δ a ≫ X.map t.leftHom.op := by
  rw [← eqToHom_map]
  simpa [SimplicialObject.δ] using
    congrArg (fun f => X.map f.op) (leftBoundaryShuffle_leftHom_eq t a)

private theorem leftBoundaryShuffle_rightHom_eq {p q : ℕ} (t : Shuffle p q)
    (a : Fin (p + 2)) :
    SimplexCategory.δ (Fin.cast (by omega) (Shuffle.leftBoundaryIndex (p := p) (q := q) t a)) ≫
      eqToHom (by rw [show p + q + 1 = (p + 1) + q by omega]) ≫
        (Shuffle.leftBoundaryShuffle (p := p) (q := q) t a).rightHom =
      t.rightHom := by
  ext k
  change Fin (p + q + 1) at k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
    OrderHom.comp_coe, Function.comp_apply, OrderEmbedding.toOrderHom_coe,
    OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply, Fin.succAboveOrderEmb_apply]
  rw [leftBoundaryIndex_succAbove_cast]
  exact congrArg Fin.val (Shuffle.rightHom_leftBoundaryShuffle_succAbove t a k)

theorem leftBoundaryShuffle_right_map {C : Type*} [CategoryTheory.Category C]
    (X : SimplicialObject C) {p q : ℕ} (t : Shuffle p q) (a : Fin (p + 2)) :
    X.map (Shuffle.leftBoundaryShuffle (p := p) (q := q) t a).rightHom.op ≫
      eqToHom (by rw [show (p + 1) + q = p + q + 1 by omega]) ≫
      X.δ (n := p + q) (Fin.cast (by omega) (Shuffle.leftBoundaryIndex (p := p) (q := q) t a)) =
      X.map t.rightHom.op := by
  rw [← eqToHom_map]
  simpa [SimplicialObject.δ] using
    congrArg (fun f => X.map f.op) (leftBoundaryShuffle_rightHom_eq t a)

private theorem rightBoundaryIndex_succAbove_cast {p q : ℕ} (t : Shuffle p q)
    (b : Fin (q + 2)) (k : Fin (p + q + 1)) :
    (Fin.cast rfl
      (Shuffle.rightBoundaryIndex (p := p) (q := q) t b)).succAbove k =
      (Shuffle.rightBoundaryIndex (p := p) (q := q) t b).succAbove
        (Fin.cast (by omega) k) := by
  apply Fin.ext
  simp only [Fin.succAbove, Fin.val_cast, Fin.val_castSucc, Fin.val_succ, apply_ite Fin.val]
  split_ifs
  all_goals simp_all [Fin.lt_def]
  omega

private theorem rightBoundaryShuffle_rightHom_eq {p q : ℕ} (t : Shuffle p q)
    (b : Fin (q + 2)) :
    SimplexCategory.δ (Fin.cast rfl (Shuffle.rightBoundaryIndex (p := p) (q := q) t b)) ≫
        (Shuffle.rightBoundaryShuffle (p := p) (q := q) t b).rightHom =
      t.rightHom ≫ SimplexCategory.δ b := by
  ext k
  change Fin (p + q + 1) at k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.len_mk,
    OrderHom.comp_coe, Function.comp_apply, OrderEmbedding.toOrderHom_coe,
    Fin.succAboveOrderEmb_apply]
  rw [rightBoundaryIndex_succAbove_cast]
  exact congrArg Fin.val (Shuffle.rightHom_rightBoundaryShuffle_succAbove t b k)

theorem rightBoundaryShuffle_right_map {C : Type*} [CategoryTheory.Category C]
    (X : SimplicialObject C) {p q : ℕ} (t : Shuffle p q) (b : Fin (q + 2)) :
    X.map (Shuffle.rightBoundaryShuffle (p := p) (q := q) t b).rightHom.op ≫
      X.δ (n := p + q) (Fin.cast rfl (Shuffle.rightBoundaryIndex (p := p) (q := q) t b)) =
      X.δ b ≫ X.map t.rightHom.op := by
  simpa [SimplicialObject.δ] using
    congrArg (fun f => X.map f.op) (rightBoundaryShuffle_rightHom_eq t b)

private theorem rightBoundaryShuffle_leftHom_eq {p q : ℕ} (t : Shuffle p q)
    (b : Fin (q + 2)) :
    SimplexCategory.δ (Fin.cast rfl (Shuffle.rightBoundaryIndex (p := p) (q := q) t b)) ≫
        (Shuffle.rightBoundaryShuffle (p := p) (q := q) t b).leftHom =
      t.leftHom := by
  ext k
  change Fin (p + q + 1) at k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.len_mk,
    OrderHom.comp_coe, Function.comp_apply, OrderEmbedding.toOrderHom_coe,
    Fin.succAboveOrderEmb_apply]
  rw [rightBoundaryIndex_succAbove_cast]
  exact congrArg Fin.val (Shuffle.leftHom_rightBoundaryShuffle_succAbove t b k)

theorem rightBoundaryShuffle_left_map {C : Type*} [CategoryTheory.Category C]
    (X : SimplicialObject C) {p q : ℕ} (t : Shuffle p q) (b : Fin (q + 2)) :
    X.map (Shuffle.rightBoundaryShuffle (p := p) (q := q) t b).leftHom.op ≫
      X.δ (n := p + q) (Fin.cast rfl (Shuffle.rightBoundaryIndex (p := p) (q := q) t b)) =
      X.map t.leftHom.op := by
  simpa [SimplicialObject.δ] using
    congrArg (fun f => X.map f.op) (rightBoundaryShuffle_leftHom_eq t b)

private theorem mixedFace_leftHom_eq {p q : ℕ} (x : Shuffle.MixedFace (p + 1) (q + 1)) :
    SimplexCategory.δ (n := (p + 1) + q) (Fin.cast (by omega) x.faceIndex) ≫ x.shuffle.leftHom =
      SimplexCategory.δ (n := (p + 1) + q) (Fin.cast (by omega) x.partner.faceIndex) ≫
        x.partner.shuffle.leftHom := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.len_mk, OrderHom.comp_coe,
    Function.comp_apply, OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  exact congrArg Fin.val (x.leftHom_partner_succAbove k)

private theorem mixedFace_rightHom_eq {p q : ℕ} (x : Shuffle.MixedFace (p + 1) (q + 1)) :
    SimplexCategory.δ (n := (p + 1) + q) (Fin.cast (by omega) x.faceIndex) ≫ x.shuffle.rightHom =
      SimplexCategory.δ (n := (p + 1) + q) (Fin.cast (by omega) x.partner.faceIndex) ≫
        x.partner.shuffle.rightHom := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.len_mk, OrderHom.comp_coe,
    Function.comp_apply, OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  exact congrArg Fin.val (x.rightHom_partner_succAbove k)

private theorem mixedFace_left_map_eq {C : Type*} [Category C]
    (X : SimplicialObject C) {p q : ℕ} (x : Shuffle.MixedFace (p + 1) (q + 1)) :
    X.map x.shuffle.leftHom.op ≫ X.δ (n := (p + 1) + q) (Fin.cast (by omega) x.faceIndex) =
      X.map x.partner.shuffle.leftHom.op ≫
        X.δ (n := (p + 1) + q) (Fin.cast (by omega) x.partner.faceIndex) := by
  simpa [SimplicialObject.δ] using congrArg (fun f => X.map f.op) (mixedFace_leftHom_eq x)

private theorem mixedFace_right_map_eq {C : Type*} [Category C]
    (X : SimplicialObject C) {p q : ℕ} (x : Shuffle.MixedFace (p + 1) (q + 1)) :
    X.map x.shuffle.rightHom.op ≫ X.δ (n := (p + 1) + q) (Fin.cast (by omega) x.faceIndex) =
      X.map x.partner.shuffle.rightHom.op ≫
        X.δ (n := (p + 1) + q) (Fin.cast (by omega) x.partner.faceIndex) := by
  simpa [SimplicialObject.δ] using congrArg (fun f => X.map f.op) (mixedFace_rightHom_eq x)

theorem mixedFace_tensor_map_eq {C : Type*} [Category C] [MonoidalCategory C]
    (X Y : SimplicialObject C) {p q : ℕ} (x : Shuffle.MixedFace (p + 1) (q + 1)) :
    MonoidalCategory.tensorHom
        (X.map x.partner.shuffle.leftHom.op ≫
          X.δ (n := (p + 1) + q) (Fin.cast (by omega) x.faceIndex))
        (Y.map x.partner.shuffle.rightHom.op ≫
          Y.δ (n := (p + 1) + q) (Fin.cast (by omega) x.faceIndex)) =
      MonoidalCategory.tensorHom
        (X.map x.shuffle.leftHom.op ≫
          X.δ (n := (p + 1) + q) (Fin.cast (by omega) x.faceIndex))
        (Y.map x.shuffle.rightHom.op ≫
          Y.δ (n := (p + 1) + q) (Fin.cast (by omega) x.faceIndex)) := by
  have hL := mixedFace_left_map_eq X x
  have hR := mixedFace_right_map_eq Y x
  rw [Shuffle.MixedFace.partner_faceIndex] at hL hR
  rw [hL, hR]

end AlgebraicTopology.EilenbergZilber
