/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.Order.Fin.Tuple

/-!
# Absolute intersections of two positive-dimensional cofaces

Two distinct faces of a simplex of dimension at least two intersect in an
original nonempty face. Their pullback square is preserved by every functor
to any universe of types. The finite retraction argument keeps the four
original coface operators and gives both equations of each pointwise filler.

This is the two-face case of Joyal, *The theory of quasi-categories*, D.0.9,
used in D.0.28. The empty intersection of the vertices of the one-simplex is
not an object of the simplex category and is outside this statement.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v

open CategoryTheory Limits
open scoped Simplicial

namespace SimplexCategory

private def cofaceRetraction {n : ℕ} (a : Fin (n + 2)) : ⦋n + 1⦌ ⟶ ⦋n⦌ :=
  if ha : a = 0 then σ 0 else σ (a.pred ha)

private theorem coface_retraction {n : ℕ} (a : Fin (n + 2)) :
    δ a ≫ cofaceRetraction a = 𝟙 _ := by
  unfold cofaceRetraction
  split_ifs with ha
  · subst a
    exact δ_comp_σ_self (i := 0)
  · simpa only [Fin.succ_pred] using δ_comp_σ_succ (i := a.pred ha)

private def towardCommonRetraction {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 3)) (h : i.castSucc < j) : ⦋n + 2⦌ ⟶ ⦋n + 1⦌ :=
  if hi : i = 0 then
    if hj : j.val = 1 then σ ⟨1, by omega⟩ else σ (j.pred h.ne_zero)
  else σ (j.pred h.ne_zero)

private theorem towardCommon_retraction {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 3)) (h : i.castSucc < j) :
    δ j ≫ towardCommonRetraction i j h = 𝟙 _ := by
  unfold towardCommonRetraction
  split_ifs with hi hj
  · have hj' : j = (⟨1, by omega⟩ : Fin (n + 3)) := Fin.ext hj
    rw [hj']
    exact δ_comp_σ_self (i := ⟨1, by omega⟩)
  · simpa only [Fin.succ_pred] using δ_comp_σ_succ (i := j.pred h.ne_zero)
  · simpa only [Fin.succ_pred] using δ_comp_σ_succ (i := j.pred h.ne_zero)

private def commonProjector {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 3)) (h : i.castSucc < j) : ⦋n + 2⦌ ⟶ ⦋n + 2⦌ :=
  cofaceRetraction i.castSucc ≫ δ i.castSucc ≫
    towardCommonRetraction i j h ≫ δ j ≫
    cofaceRetraction i.castSucc ≫ δ i.castSucc ≫
    towardCommonRetraction i j h ≫ δ j

private theorem cofaceProjector_val {n : ℕ} (a : Fin (n + 2))
    (x : Fin (n + 2)) :
    ((cofaceRetraction a ≫ δ a).toOrderHom x).val =
      if x = a then if a = 0 then 1 else a.val - 1 else x.val := by
  by_cases ha : a = 0
  · subst a
    simp only [cofaceRetraction]
    by_cases hx : x = 0
    · subst x
      rfl
    · change (Fin.succ (Fin.predAbove (0 : Fin (n + 1)) x)).val = _
      rw [Fin.predAbove_zero_of_ne_zero hx, Fin.succ_pred]
      simp only [ite_eq_right hx]
  · simp only [cofaceRetraction, dite_eq_right ha]
    by_cases hx : x = a
    · subst x
      change (a.succAbove ((a.pred ha).predAbove a)).val = _
      rw [Fin.predAbove_pred_self, Fin.succAbove_pred_self]
      simp only [ite_eq_right ha, Fin.val_castSucc, Fin.val_pred, ite_true]
    · change (a.succAbove ((a.pred ha).predAbove x)).val = _
      have he := Fin.succ_succAbove_predAbove (p := a.pred ha) (i := x)
        (by simpa only [Fin.succ_pred] using hx)
      rw [Fin.succ_pred] at he
      rw [he]
      simp only [ite_eq_right hx]

private theorem towardCommonProjector_val {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 3)) (h : i.castSucc < j) (x : Fin (n + 3)) :
    ((towardCommonRetraction i j h ≫ δ j).toOrderHom x).val =
      if x = j then if i = 0 ∧ j.val = 1 then 2 else j.val - 1 else x.val := by
  by_cases hi : i = 0
  · by_cases hj : j.val = 1
    · simp only [towardCommonRetraction, dite_eq_left hi, dite_eq_left hj]
      let k : Fin (n + 2) := ⟨1, by omega⟩
      have hj' : j = k.castSucc := Fin.ext hj
      rw [hj']
      by_cases hx : x = k.castSucc
      · subst x
        change (k.castSucc.succAbove (k.predAbove k.castSucc)).val = _
        rw [Fin.predAbove_castSucc_self, Fin.succAbove_castSucc_self]
        simp only [Fin.val_succ, k, hi, ite_true, true_and]
        rfl
      · change (k.castSucc.succAbove (k.predAbove x)).val = _
        rw [Fin.succAbove_predAbove hx]
        simp only [ite_eq_right hx]
    · have heq : towardCommonRetraction i j h = cofaceRetraction j := by
        simp only [towardCommonRetraction, dite_eq_left hi, dite_eq_right hj,
          cofaceRetraction, dite_eq_right h.ne_zero]
      rw [heq, cofaceProjector_val]
      simp only [ite_eq_right h.ne_zero, hi, hj, and_false, ite_false]
  · have heq : towardCommonRetraction i j h = cofaceRetraction j := by
      simp only [towardCommonRetraction, dite_eq_right hi,
        cofaceRetraction, dite_eq_right h.ne_zero]
    rw [heq, cofaceProjector_val]
    simp only [ite_eq_right h.ne_zero, hi, false_and, ite_false]

private theorem commonProjector_avoids {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 3)) (h : i.castSucc < j) (x : Fin (n + 3)) :
    (commonProjector i j h).toOrderHom x ≠ i.castSucc ∧
      (commonProjector i j h).toOrderHom x ≠ j := by
  let ei := cofaceRetraction i.castSucc ≫ δ i.castSucc
  let ej := towardCommonRetraction i j h ≫ δ j
  let x1 := ei.toOrderHom x
  let x2 := ej.toOrderHom x1
  let x3 := ei.toOrderHom x2
  let x4 := ej.toOrderHom x3
  have h1 := cofaceProjector_val i.castSucc x
  have h2 := towardCommonProjector_val i j h x1
  have h3 := cofaceProjector_val i.castSucc x2
  have h4 := towardCommonProjector_val i j h x3
  change x1.val = _ at h1
  change x2.val = _ at h2
  change x3.val = _ at h3
  change x4.val = _ at h4
  simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_zero] at h1 h2 h3 h4
  have hij : i.val < j.val := h
  have ha : i.castSucc.val = i.val := rfl
  change x4 ≠ i.castSucc ∧ x4 ≠ j
  constructor
  all_goals
    apply Fin.ne_of_val_ne
    split_ifs at h1 h2 h3 h4 <;> omega

private theorem commonProjector_fixes {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 3)) (h : i.castSucc < j) :
    (δ (j.pred h.ne_zero) ≫ δ i.castSucc) ≫ commonProjector i j h =
      δ (j.pred h.ne_zero) ≫ δ i.castSucc := by
  let b := δ (j.pred h.ne_zero) ≫ δ i.castSucc
  have hi : b ≫ cofaceRetraction i.castSucc ≫ δ i.castSucc = b := by
    dsimp only [b]
    rw [Category.assoc, ← Category.assoc (δ i.castSucc), coface_retraction,
      Category.id_comp]
  have hj : b ≫ towardCommonRetraction i j h ≫ δ j = b := by
    dsimp only [b]
    rw [← δ_comp_δ' h, Category.assoc, ← Category.assoc (δ j),
      towardCommon_retraction, Category.id_comp]
  change b ≫ commonProjector i j h = b
  unfold commonProjector
  simp only [← Category.assoc]
  simp only [← Category.assoc] at hi hj
  rw [hi, hj, hi, hj]

private def firstFaceFactor {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 3)) (h : i.castSucc < j) : Fin (n + 3) →o Fin (n + 2) where
  toFun x := (finSuccAboveOrderIso i.castSucc).symm
    ⟨(commonProjector i j h).toOrderHom x, (commonProjector_avoids i j h x).1⟩
  monotone' := (finSuccAboveOrderIso i.castSucc).symm.monotone.comp
    (commonProjector i j h).toOrderHom.monotone

private theorem firstFaceFactor_equation {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 3)) (h : i.castSucc < j) (x : Fin (n + 3)) :
    i.castSucc.succAbove (firstFaceFactor i j h x) =
      (commonProjector i j h).toOrderHom x := by
  exact congrArg Subtype.val ((finSuccAboveOrderIso i.castSucc).apply_symm_apply _)

private theorem firstFaceFactor_avoids {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 3)) (h : i.castSucc < j) (x : Fin (n + 3)) :
    firstFaceFactor i j h x ≠ j.pred h.ne_zero := by
  intro he
  have hj : i.castSucc.succAbove (j.pred h.ne_zero) = j :=
    Fin.succAbove_pred_of_lt _ _ h
  apply (commonProjector_avoids i j h x).2
  rw [← firstFaceFactor_equation i j h x, he, hj]

private def commonRetraction {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 3)) (h : i.castSucc < j) : ⦋n + 2⦌ ⟶ ⦋n⦌ :=
  mkHom {
    toFun := fun x => (finSuccAboveOrderIso (j.pred h.ne_zero)).symm
      ⟨firstFaceFactor i j h x, firstFaceFactor_avoids i j h x⟩
    monotone' := (finSuccAboveOrderIso (j.pred h.ne_zero)).symm.monotone.comp
      (firstFaceFactor i j h).monotone
  }

private theorem commonRetraction_projector {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 3)) (h : i.castSucc < j) :
    commonRetraction i j h ≫ (δ (j.pred h.ne_zero) ≫ δ i.castSucc) =
      commonProjector i j h := by
  apply Hom.ext'
  apply OrderHom.ext
  apply funext
  intro x
  change i.castSucc.succAbove
    ((j.pred h.ne_zero).succAbove
      ((finSuccAboveOrderIso (j.pred h.ne_zero)).symm
        ⟨firstFaceFactor i j h x, firstFaceFactor_avoids i j h x⟩)) = _
  rw [show (j.pred h.ne_zero).succAbove
      ((finSuccAboveOrderIso (j.pred h.ne_zero)).symm
        ⟨firstFaceFactor i j h x, firstFaceFactor_avoids i j h x⟩) =
      firstFaceFactor i j h x from
    congrArg Subtype.val ((finSuccAboveOrderIso (j.pred h.ne_zero)).apply_symm_apply _)]
  exact firstFaceFactor_equation i j h x

private theorem commonRetraction_splits {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 3)) (h : i.castSucc < j) :
    (δ (j.pred h.ne_zero) ≫ δ i.castSucc) ≫ commonRetraction i j h = 𝟙 _ := by
  apply (cancel_mono (δ (j.pred h.ne_zero) ≫ δ i.castSucc)).mp
  rw [Category.assoc, commonRetraction_projector, commonProjector_fixes,
    Category.id_comp]

/-- Every Type-valued functor preserves the original intersection square of two
cofaces whose target has dimension at least two. -/
theorem absoluteCofacePullback (H : SimplexCategory ⥤ Type v) {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 3)) (h : i.castSucc < j) :
    IsPullback (H.map (δ (j.pred h.ne_zero))) (H.map (δ i))
      (H.map (δ i.castSucc)) (H.map (δ j)) := by
  let p := δ (j.pred h.ne_zero)
  let q := δ i
  let u := δ i.castSucc
  let v := δ j
  let b := p ≫ u
  let r := commonRetraction i j h
  have hu : Function.LeftInverse (H.map (cofaceRetraction i.castSucc)) (H.map u) := by
    intro x
    change (H.map u ≫ H.map (cofaceRetraction i.castSucc)) x = x
    rw [← H.map_comp, coface_retraction, H.map_id]
    rfl
  have hv : Function.LeftInverse (H.map (towardCommonRetraction i j h)) (H.map v) := by
    intro x
    change (H.map v ≫ H.map (towardCommonRetraction i j h)) x = x
    rw [← H.map_comp, towardCommon_retraction, H.map_id]
    rfl
  have hb : Function.LeftInverse (H.map r) (H.map b) := by
    intro x
    change (H.map b ≫ H.map r) x = x
    rw [← H.map_comp, commonRetraction_splits, H.map_id]
    rfl
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [← H.map_comp, ← H.map_comp, δ_comp_δ' h]
  · intro x y hxy
    apply hb.injective
    dsimp only [b]
    rw [H.map_comp]
    change (H.map p ≫ H.map u) x = (H.map p ≫ H.map u) y
    exact congrArg (H.map u) hxy.1
  · intro x y hxy
    let z := H.map u x
    have hei : H.map (cofaceRetraction i.castSucc ≫ u) z = z := by
      rw [H.map_comp]
      change H.map u (H.map (cofaceRetraction i.castSucc) (H.map u x)) = H.map u x
      rw [hu x]
    have hej : H.map (towardCommonRetraction i j h ≫ v) z = z := by
      change H.map (towardCommonRetraction i j h ≫ v) (H.map u x) = H.map u x
      rw [hxy, H.map_comp]
      change H.map v (H.map (towardCommonRetraction i j h) (H.map v y)) = H.map v y
      rw [hv y]
    have he : H.map (commonProjector i j h) z = z := by
      let ei := cofaceRetraction i.castSucc ≫ u
      let ej := towardCommonRetraction i j h ≫ v
      have hp : commonProjector i j h = ei ≫ ej ≫ ei ≫ ej := by
        dsimp only [commonProjector, ei, ej, u, v]
        simp only [Category.assoc]
      rw [hp, H.map_comp ei (ej ≫ ei ≫ ej), types_comp_apply, hei,
        H.map_comp ej (ei ≫ ej), types_comp_apply, hej,
        H.map_comp ei ej, types_comp_apply, hei, hej]
    refine ⟨H.map r z, ?_, ?_⟩
    · apply hu.injective
      change (H.map p ≫ H.map u) (H.map r z) = z
      rw [← H.map_comp]
      change (H.map r ≫ H.map b) z = z
      rw [← H.map_comp, commonRetraction_projector]
      exact he
    · apply hv.injective
      change (H.map q ≫ H.map v) (H.map r z) = H.map v y
      rw [← H.map_comp, δ_comp_δ' h, ← hxy]
      change (H.map r ≫ H.map b) z = z
      rw [← H.map_comp, commonRetraction_projector]
      exact he

/-- A compatible original pair has an original corner point with both coface
equations, and those equations determine that point uniquely. -/
theorem existsUnique_cofaceFiller (H : SimplexCategory ⥤ Type v) {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 3)) (h : i.castSucc < j)
    (x y : H.obj ⦋n + 1⦌) (hxy : H.map (δ i.castSucc) x = H.map (δ j) y) :
    ∃! z : H.obj ⦋n⦌, H.map (δ (j.pred h.ne_zero)) z = x ∧ H.map (δ i) z = y := by
  have hp := absoluteCofacePullback H i j h
  obtain ⟨z, hz⟩ := Types.exists_of_isPullback hp x y hxy
  refine ⟨z, hz, ?_⟩
  intro z' hz'
  exact Types.ext_of_isPullback hp (hz'.1.trans hz.1.symm) (hz'.2.trans hz.2.symm)

end SimplexCategory
