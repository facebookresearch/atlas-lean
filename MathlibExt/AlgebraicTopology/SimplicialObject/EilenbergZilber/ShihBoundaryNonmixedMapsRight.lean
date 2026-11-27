/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryNonmixedValuesRight

/-!
# Inserted-right nonmixed Shih boundary maps

The coordinate computations are lifted to the two simplex words and then to
maps of an arbitrary simplicial object.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Simplicial

universe v u

namespace AlgebraicTopology.EilenbergZilber.ShihIndex

set_option backward.isDefEq.respectTransparency false in
/-- Left simplex word for a positive inserted-right boundary. -/
theorem rightBoundaryUpper_leftWord
    (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2)) (hb : 0 < b.val) :
    (rightBoundaryUpperIndex p q m hm t b).leftHom.op ≫
        (SimplexCategory.δ (rightBoundaryUpperFace p q m t b)).op =
      (SimplexCategory.δ (rightBoundaryLowerFace p q m b hb)).op ≫
        (ofGap p q m hm t).leftHom.op := by
  apply Quiver.Hom.unop_inj
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext x
  simp only [leftHom, SimplexCategory.δ, SimplexCategory.mkHom,
    gap_rightBoundaryUpperIndex, gap_ofGap]
  change
    (if _h : ((rightBoundaryUpperFace p q m t b).succAbove x).val < m
      then _ else _) =
      (rightBoundaryLowerFace p q m b hb).succAbove
        (if _h : x.val < m then _ else _)
  by_cases hx : x.val < m
  · have hface : x.castSucc < rightBoundaryUpperFace p q m t b := by
      simp only [Fin.lt_def, Fin.val_castSucc, rightBoundaryUpperFace]
      omega
    have hupper :
        ((rightBoundaryUpperFace p q m t b).succAbove x).val < m := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hface]
      simpa only [Fin.val_castSucc] using hx
    rw [dite_eq_left hupper, dite_eq_left hx]
    let xl : Fin (p + q + m + 1) := ⟨x.val, by
      have hxlt := x.isLt
      omega⟩
    apply Fin.ext
    change ((rightBoundaryUpperFace p q m t b).succAbove x).val =
      ((rightBoundaryLowerFace p q m b hb).succAbove xl).val
    have hlower : xl.castSucc < rightBoundaryLowerFace p q m b hb := by
      simp only [Fin.lt_def, Fin.val_castSucc, rightBoundaryLowerFace, xl]
      omega
    rw [Fin.succAbove_of_castSucc_lt _ _ hface,
      Fin.succAbove_of_castSucc_lt _ _ hlower]
    rfl
  · have hxm : m ≤ x.val := le_of_not_gt hx
    have hupper : ¬
        ((rightBoundaryUpperFace p q m t b).succAbove x).val < m := by
      by_cases hface : x.castSucc < rightBoundaryUpperFace p q m t b
      · rw [Fin.succAbove_of_castSucc_lt _ _ hface]
        simp only [Fin.val_castSucc]
        omega
      · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hface)]
        simp only [Fin.val_succ]
        omega
    rw [dite_eq_right hupper, dite_eq_right hx]
    apply Fin.ext
    have hvalue := rightBoundaryUpper_leftValue p q m hm t b x hxm
    let l : Fin (p + 2) := Fin.cast (by simp [ofGap])
      ((ofGap p q m hm t).shuffle.leftHom.toOrderHom
        ((ofGap p q m hm t).suffixInput x (by simpa only [gap_ofGap] using hxm)))
    let y : Fin (p + q + m + 1) := ⟨m - 1 + l.val, by
      have hl := l.isLt
      omega⟩
    change m - 1 + _ =
      ((rightBoundaryLowerFace p q m b hb).succAbove y).val
    simp only [Quiver.Hom.unop_op, SimplexCategory.Hom.toOrderHom_mk,
      OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
    rw [hvalue]
    have hy : y.castSucc < rightBoundaryLowerFace p q m b hb := by
      simp only [Fin.lt_def, Fin.val_castSucc, rightBoundaryLowerFace, y]
      have hl := l.isLt
      omega
    rw [Fin.succAbove_of_castSucc_lt _ _ hy]
    rfl

variable {C : Type u} [Category.{v} C]

/-- Left-factor map comparison for a positive inserted-right boundary. -/
theorem map_rightBoundaryUpper_leftHom_comp_delta
    (X : SimplicialObject C) (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2)) (hb : 0 < b.val) :
    X.map (rightBoundaryUpperIndex p q m hm t b).leftHom.op ≫
        X.δ (rightBoundaryUpperFace p q m t b) =
      X.δ (rightBoundaryLowerFace p q m b hb) ≫
        X.map (ofGap p q m hm t).leftHom.op := by
  simpa only [X.δ_def, ← X.map_comp] using congrArg (fun f => X.map f)
    (rightBoundaryUpper_leftWord p q m hm t b hb)

set_option backward.isDefEq.respectTransparency false in
/-- Right simplex word for a positive inserted-right boundary. -/
theorem rightBoundaryUpper_rightWord
    (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2)) (hb : 0 < b.val) :
    (rightBoundaryUpperIndex p q m hm t b).rightHom.op ≫
        (SimplexCategory.δ (rightBoundaryUpperFace p q m t b)).op =
      (SimplexCategory.δ (rightBoundaryLowerFace p q m b hb)).op ≫
        (ofGap p q m hm t).rightHom.op := by
  apply Quiver.Hom.unop_inj
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext x
  simp only [rightHom, SimplexCategory.δ, SimplexCategory.mkHom,
    gap_rightBoundaryUpperIndex, gap_ofGap]
  change
    (if _h : ((rightBoundaryUpperFace p q m t b).succAbove x).val < m
      then _ else _) =
      (rightBoundaryLowerFace p q m b hb).succAbove
        (if _h : x.val < m then _ else _)
  by_cases hx : x.val < m
  · have hface : x.castSucc < rightBoundaryUpperFace p q m t b := by
      simp only [Fin.lt_def, Fin.val_castSucc, rightBoundaryUpperFace]
      omega
    have hupper :
        ((rightBoundaryUpperFace p q m t b).succAbove x).val < m := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hface]
      simpa only [Fin.val_castSucc] using hx
    rw [dite_eq_left hupper, dite_eq_left hx]
    let xl : Fin (p + q + m + 1) := ⟨x.val, by
      have hxlt := x.isLt
      omega⟩
    apply Fin.ext
    change ((rightBoundaryUpperFace p q m t b).succAbove x).val =
      ((rightBoundaryLowerFace p q m b hb).succAbove xl).val
    have hlower : xl.castSucc < rightBoundaryLowerFace p q m b hb := by
      simp only [Fin.lt_def, Fin.val_castSucc, rightBoundaryLowerFace, xl]
      omega
    rw [Fin.succAbove_of_castSucc_lt _ _ hface,
      Fin.succAbove_of_castSucc_lt _ _ hlower]
    rfl
  · have hxm : m ≤ x.val := le_of_not_gt hx
    have hupper : ¬
        ((rightBoundaryUpperFace p q m t b).succAbove x).val < m := by
      by_cases hface : x.castSucc < rightBoundaryUpperFace p q m t b
      · rw [Fin.succAbove_of_castSucc_lt _ _ hface]
        simp only [Fin.val_castSucc]
        omega
      · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hface)]
        simp only [Fin.val_succ]
        omega
    rw [dite_eq_right hupper, dite_eq_right hx]
    apply Fin.ext
    have hvalue := rightBoundaryUpper_rightValue p q m hm t b x hxm
    let r : Fin (q + 1) := Fin.cast (by simp [ofGap])
      ((ofGap p q m hm t).shuffle.rightHom.toOrderHom
        ((ofGap p q m hm t).suffixInput x (by simpa only [gap_ofGap] using hxm)))
    let y : Fin (p + q + m + 1) := ⟨m + p + r.val, by
      have hr := r.isLt
      omega⟩
    change m + p + _ =
      ((rightBoundaryLowerFace p q m b hb).succAbove y).val
    simp only [Quiver.Hom.unop_op, SimplexCategory.Hom.toOrderHom_mk,
      OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
    rw [hvalue]
    change m + p + (b.succAbove r).val =
      ((rightBoundaryLowerFace p q m b hb).succAbove y).val
    by_cases hrb : r.castSucc < b
    · have hy : y.castSucc < rightBoundaryLowerFace p q m b hb := by
        simp only [Fin.lt_def, Fin.val_castSucc, rightBoundaryLowerFace, y]
        simp only [Fin.lt_def, Fin.val_castSucc] at hrb
        omega
      rw [Fin.succAbove_of_castSucc_lt _ _ hrb,
        Fin.succAbove_of_castSucc_lt _ _ hy]
      rfl
    · have hy : rightBoundaryLowerFace p q m b hb ≤ y.castSucc := by
        simp only [Fin.le_def, Fin.val_castSucc, rightBoundaryLowerFace, y]
        simp only [Fin.lt_def, Fin.val_castSucc] at hrb
        omega
      rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hrb),
        Fin.succAbove_of_le_castSucc _ _ hy]
      rfl

/-- Right-factor map comparison for a positive inserted-right boundary. -/
theorem map_rightBoundaryUpper_rightHom_comp_delta
    (X : SimplicialObject C) (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2)) (hb : 0 < b.val) :
    X.map (rightBoundaryUpperIndex p q m hm t b).rightHom.op ≫
        X.δ (rightBoundaryUpperFace p q m t b) =
      X.δ (rightBoundaryLowerFace p q m b hb) ≫
        X.map (ofGap p q m hm t).rightHom.op := by
  simpa only [X.δ_def, ← X.map_comp] using congrArg (fun f => X.map f)
    (rightBoundaryUpper_rightWord p q m hm t b hb)

end AlgebraicTopology.EilenbergZilber.ShihIndex
