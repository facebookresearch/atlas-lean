/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryNonmixedValuesLeft

/-!
# Inserted-left nonmixed Shih boundary maps

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
/-- Left simplex word for an interior inserted-left boundary. -/
theorem leftBoundaryUpper_leftWord
    (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3))
    (ha0 : 0 < a.val) :
    (leftBoundaryUpperIndex p q m hm t a).leftHom.op ≫
        (SimplexCategory.δ (leftBoundaryUpperFace p q m t a)).op =
      (SimplexCategory.δ (leftBoundaryLowerFace p q m hm a ha0)).op ≫
        (ofGap p q m hm t).leftHom.op := by
  apply Quiver.Hom.unop_inj
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext x
  simp only [leftHom, SimplexCategory.δ, SimplexCategory.mkHom,
    gap_leftBoundaryUpperIndex, gap_ofGap]
  change
    (if _h : ((leftBoundaryUpperFace p q m t a).succAbove x).val < m
      then _ else _) =
      (leftBoundaryLowerFace p q m hm a ha0).succAbove
        (if _h : x.val < m then _ else _)
  by_cases hx : x.val < m
  · have hface : x.castSucc < leftBoundaryUpperFace p q m t a := by
      simp only [Fin.lt_def, Fin.val_castSucc, leftBoundaryUpperFace]
      omega
    have hupper :
        ((leftBoundaryUpperFace p q m t a).succAbove x).val < m := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hface]
      simpa only [Fin.val_castSucc] using hx
    rw [dite_eq_left hupper, dite_eq_left hx]
    let xl : Fin (p + q + m + 1) := ⟨x.val, by
      have hxlt := x.isLt
      omega⟩
    apply Fin.ext
    change ((leftBoundaryUpperFace p q m t a).succAbove x).val =
      ((leftBoundaryLowerFace p q m hm a ha0).succAbove xl).val
    have hlower : xl.castSucc < leftBoundaryLowerFace p q m hm a ha0 := by
      simp only [Fin.lt_def, Fin.val_castSucc, leftBoundaryLowerFace, xl]
      omega
    rw [Fin.succAbove_of_castSucc_lt _ _ hface,
      Fin.succAbove_of_castSucc_lt _ _ hlower]
    rfl
  · have hxm : m ≤ x.val := le_of_not_gt hx
    have hupper : ¬
        ((leftBoundaryUpperFace p q m t a).succAbove x).val < m := by
      by_cases hface : x.castSucc < leftBoundaryUpperFace p q m t a
      · rw [Fin.succAbove_of_castSucc_lt _ _ hface]
        simp only [Fin.val_castSucc]
        omega
      · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hface)]
        simp only [Fin.val_succ]
        omega
    rw [dite_eq_right hupper, dite_eq_right hx]
    apply Fin.ext
    have hvalue := leftBoundaryUpper_leftValue p q m hm t a x hxm
    let l : Fin (p + 2) := Fin.cast (by simp [ofGap])
      ((ofGap p q m hm t).shuffle.leftHom.toOrderHom
        ((ofGap p q m hm t).suffixInput x (by simpa only [gap_ofGap] using hxm)))
    have hvalue' := hvalue
    change _ = (a.succAbove l).val at hvalue'
    let y : Fin (p + q + m + 1) := ⟨m - 1 + l.val, by
      have hl := l.isLt
      omega⟩
    change m - 1 + _ =
      ((leftBoundaryLowerFace p q m hm a ha0).succAbove y).val
    simp only [Quiver.Hom.unop_op, SimplexCategory.Hom.toOrderHom_mk,
      OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
    rw [hvalue']
    by_cases hla : l.castSucc < a
    · rw [Fin.succAbove_of_castSucc_lt _ _ hla]
      have hylower : y.castSucc < leftBoundaryLowerFace p q m hm a ha0 := by
        simp only [Fin.lt_def, Fin.val_castSucc, leftBoundaryLowerFace, y]
        exact Nat.add_lt_add_left (Fin.lt_def.mp hla) (m - 1)
      rw [Fin.succAbove_of_castSucc_lt _ _ hylower]
      simp only [Fin.val_castSucc, y, l, Fin.val_cast]
    · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hla)]
      have hylower : leftBoundaryLowerFace p q m hm a ha0 ≤ y.castSucc := by
        simp only [Fin.le_def, Fin.val_castSucc, leftBoundaryLowerFace, y]
        exact Nat.add_le_add_left
          (Fin.le_iff_val_le_val.mp (le_of_not_gt hla)) (m - 1)
      rw [Fin.succAbove_of_le_castSucc _ _ hylower]
      simp only [Fin.val_succ, y, l, Fin.val_cast]
      omega

variable {C : Type u} [Category.{v} C]

/-- Left-factor map comparison for an interior inserted-left boundary. -/
theorem map_leftBoundaryUpper_leftHom_comp_delta
    (X : SimplicialObject C) (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3))
    (ha0 : 0 < a.val) :
    X.map (leftBoundaryUpperIndex p q m hm t a).leftHom.op ≫
        X.δ (leftBoundaryUpperFace p q m t a) =
      X.δ (leftBoundaryLowerFace p q m hm a ha0) ≫
        X.map (ofGap p q m hm t).leftHom.op := by
  simpa only [X.δ_def, ← X.map_comp] using congrArg (fun f => X.map f)
    (leftBoundaryUpper_leftWord p q m hm t a ha0)

set_option backward.isDefEq.respectTransparency false in
/-- Right simplex word for an interior inserted-left boundary. -/
theorem leftBoundaryUpper_rightWord
    (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3))
    (ha0 : 0 < a.val) (haLast : a.val < p + 2) :
    (leftBoundaryUpperIndex p q m hm t a).rightHom.op ≫
        (SimplexCategory.δ (leftBoundaryUpperFace p q m t a)).op =
      (SimplexCategory.δ (leftBoundaryLowerFace p q m hm a ha0)).op ≫
        (ofGap p q m hm t).rightHom.op := by
  apply Quiver.Hom.unop_inj
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext x
  simp only [rightHom, SimplexCategory.δ, SimplexCategory.mkHom,
    gap_leftBoundaryUpperIndex, gap_ofGap]
  change
    (if _h : ((leftBoundaryUpperFace p q m t a).succAbove x).val < m
      then _ else _) =
      (leftBoundaryLowerFace p q m hm a ha0).succAbove
        (if _h : x.val < m then _ else _)
  by_cases hx : x.val < m
  · have hface : x.castSucc < leftBoundaryUpperFace p q m t a := by
      simp only [Fin.lt_def, Fin.val_castSucc, leftBoundaryUpperFace]
      omega
    have hupper :
        ((leftBoundaryUpperFace p q m t a).succAbove x).val < m := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hface]
      simpa only [Fin.val_castSucc] using hx
    rw [dite_eq_left hupper, dite_eq_left hx]
    let xl : Fin (p + q + m + 1) := ⟨x.val, by
      have hxlt := x.isLt
      omega⟩
    apply Fin.ext
    change ((leftBoundaryUpperFace p q m t a).succAbove x).val =
      ((leftBoundaryLowerFace p q m hm a ha0).succAbove xl).val
    have hlower : xl.castSucc < leftBoundaryLowerFace p q m hm a ha0 := by
      simp only [Fin.lt_def, Fin.val_castSucc, leftBoundaryLowerFace, xl]
      omega
    rw [Fin.succAbove_of_castSucc_lt _ _ hface,
      Fin.succAbove_of_castSucc_lt _ _ hlower]
    rfl
  · have hxm : m ≤ x.val := le_of_not_gt hx
    have hupper : ¬
        ((leftBoundaryUpperFace p q m t a).succAbove x).val < m := by
      by_cases hface : x.castSucc < leftBoundaryUpperFace p q m t a
      · rw [Fin.succAbove_of_castSucc_lt _ _ hface]
        simp only [Fin.val_castSucc]
        omega
      · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hface)]
        simp only [Fin.val_succ]
        omega
    rw [dite_eq_right hupper, dite_eq_right hx]
    apply Fin.ext
    have hvalue := leftBoundaryUpper_rightValue p q m hm t a x hxm
    let r : Fin (q + 1) := Fin.cast (by simp [ofGap])
      ((ofGap p q m hm t).shuffle.rightHom.toOrderHom
        ((ofGap p q m hm t).suffixInput x (by simpa only [gap_ofGap] using hxm)))
    have hvalue' := hvalue
    change _ = r.val at hvalue'
    let y : Fin (p + q + m + 1) := ⟨m + p + r.val, by
      have hr := r.isLt
      omega⟩
    change m + (p + 1) + _ =
      ((leftBoundaryLowerFace p q m hm a ha0).succAbove y).val
    simp only [Quiver.Hom.unop_op, SimplexCategory.Hom.toOrderHom_mk,
      OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
    rw [hvalue']
    have hlower : leftBoundaryLowerFace p q m hm a ha0 ≤ y.castSucc := by
      simp only [Fin.le_def, Fin.val_castSucc, leftBoundaryLowerFace, y]
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ hlower]
    simp only [Fin.val_succ, y]
    omega

/-- Right-factor map comparison for an interior inserted-left boundary. -/
theorem map_leftBoundaryUpper_rightHom_comp_delta
    (X : SimplicialObject C) (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3))
    (ha0 : 0 < a.val) (haLast : a.val < p + 2) :
    X.map (leftBoundaryUpperIndex p q m hm t a).rightHom.op ≫
        X.δ (leftBoundaryUpperFace p q m t a) =
      X.δ (leftBoundaryLowerFace p q m hm a ha0) ≫
        X.map (ofGap p q m hm t).rightHom.op := by
  simpa only [X.δ_def, ← X.map_comp] using congrArg (fun f => X.map f)
    (leftBoundaryUpper_rightWord p q m hm t a ha0 haLast)

end AlgebraicTopology.EilenbergZilber.ShihIndex
