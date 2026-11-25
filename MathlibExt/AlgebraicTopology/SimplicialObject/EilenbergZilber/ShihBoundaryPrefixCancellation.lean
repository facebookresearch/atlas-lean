/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryExpansion

/-!
# Prefix-face cancellation in the Shih boundary

This file pairs the boundary terms whose face lies strictly before the active
Shih block.  Passing from the upper to the lower term shortens the inactive
prefix by one and reverses the sign.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

namespace ShihIndex

/-- Shorten the inactive prefix of a Shih index by one. -/
def lowerPrefix {n : ℕ} (i : ShihIndex (n + 1)) (h : 1 < i.gap) : ShihIndex n where
  p := ⟨i.p, by
    have hi := i.p_add_q_add_gap
    omega⟩
  q := ⟨i.q, by
    change (i.q : ℕ) < n - (i.p : ℕ)
    have hi := i.p_add_q_add_gap
    omega⟩
  shuffle := i.shuffle

/-- Reinterpret a face strictly before the shortened prefix in one lower
degree. -/
def lowerPrefixFace {n : ℕ} (i : ShihIndex (n + 1)) (k : Fin (n + 3))
    (h : k.val + 1 < i.gap) : Fin (n + 2) :=
  ⟨k.val, by
    have hi := i.p_add_q_add_gap
    omega⟩

/-- Lengthen the inactive prefix of a Shih index by one. -/
def raisePrefix {n : ℕ} (i : ShihIndex n) : ShihIndex (n + 1) where
  p := ⟨i.p, by
    omega⟩
  q := ⟨i.q, by
    change (i.q : ℕ) < n + 1 - (i.p : ℕ)
    have hi := i.q.isLt
    omega⟩
  shuffle := i.shuffle

@[simp]
theorem gap_lowerPrefix {n : ℕ} (i : ShihIndex (n + 1)) (h : 1 < i.gap) :
    (i.lowerPrefix h).gap + 1 = i.gap := by
  simp only [lowerPrefix, gap]
  have hi := i.p_add_q_add_gap
  omega

@[simp]
theorem gap_raisePrefix {n : ℕ} (i : ShihIndex n) :
    i.raisePrefix.gap = i.gap + 1 := by
  simp only [raisePrefix, gap]
  have hi := i.p_add_q_add_gap
  omega

theorem sign_lowerPrefix {n : ℕ} (i : ShihIndex (n + 1)) (h : 1 < i.gap) :
    (i.lowerPrefix h).sign = -i.sign := by
  unfold sign
  rw [i.gap_lowerPrefix h, pow_succ]
  simp only [lowerPrefix]
  ring

end ShihIndex

/-- Upper boundary indices whose face lies strictly before the active Shih
block. -/
def ShihUpperPrefixIndex (n : ℕ) :=
  {z : Fin (n + 3) × ShihIndex (n + 1) // z.1.val + 1 < z.2.gap}

/-- Lower boundary indices with the same face in the shortened inactive
prefix. -/
def ShihLowerPrefixIndex (n : ℕ) :=
  {z : ShihIndex n × Fin (n + 2) // z.2.val < z.1.gap}

noncomputable instance (n : ℕ) : Fintype (ShihUpperPrefixIndex n) := by
  unfold ShihUpperPrefixIndex
  infer_instance

noncomputable instance (n : ℕ) : Fintype (ShihLowerPrefixIndex n) := by
  unfold ShihLowerPrefixIndex
  infer_instance

def shihUpperPrefixToLower (n : ℕ) :
    ShihUpperPrefixIndex n → ShihLowerPrefixIndex n := by
  rintro ⟨⟨k, i⟩, hz⟩
  change k.val + 1 < i.gap at hz
  have hi : 1 < i.gap := by omega
  refine ⟨⟨i.lowerPrefix hi, i.lowerPrefixFace k hz⟩, ?_⟩
  change k.val < (i.lowerPrefix hi).gap
  have hgap := i.gap_lowerPrefix hi
  omega

def shihLowerPrefixToUpper (n : ℕ) :
    ShihLowerPrefixIndex n → ShihUpperPrefixIndex n := by
  rintro ⟨⟨i, k⟩, hz⟩
  change k.val < i.gap at hz
  refine ⟨⟨⟨k.val, by omega⟩, i.raisePrefix⟩, ?_⟩
  change k.val + 1 < i.raisePrefix.gap
  have hgap := i.gap_raisePrefix
  omega

/-- Removing one inactive prefix vertex pairs upper prefix faces with lower
prefix faces. -/
def shihUpperPrefixEquivLowerPrefix (n : ℕ) :
    ShihUpperPrefixIndex n ≃ ShihLowerPrefixIndex n where
  toFun := shihUpperPrefixToLower n
  invFun := shihLowerPrefixToUpper n
  left_inv z := by
    rcases z with ⟨⟨k, ⟨p, q, s⟩⟩, hz⟩
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      rfl
    · rfl
  right_inv z := by
    rcases z with ⟨⟨⟨p, q, s⟩, k⟩, hz⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      rfl

@[simp]
theorem shihUpperPrefixEquivLowerPrefix_face_val (n : ℕ)
    (z : ShihUpperPrefixIndex n) :
    ((shihUpperPrefixEquivLowerPrefix n z).val.2).val = z.val.1.val := rfl

theorem shihUpperPrefixEquivLowerPrefix_sign (n : ℕ)
    (z : ShihUpperPrefixIndex n) :
    (shihUpperPrefixEquivLowerPrefix n z).val.1.sign = -z.val.2.sign := by
  rcases z with ⟨⟨k, i⟩, hz⟩
  change k.val + 1 < i.gap at hz
  exact i.sign_lowerPrefix (by omega)

theorem delta_comp_leftHom_lowerPrefix {n : ℕ} (i : ShihIndex (n + 1))
    (k : Fin (n + 3)) (hk : k.val + 1 < i.gap) :
    SimplexCategory.δ k ≫ i.leftHom =
      (i.lowerPrefix (by omega)).leftHom ≫
        SimplexCategory.δ (i.lowerPrefixFace k hk) := by
  have hi : 1 < i.gap := by omega
  change SimplexCategory.δ k ≫ i.leftHom =
    (i.lowerPrefix hi).leftHom ≫ SimplexCategory.δ (i.lowerPrefixFace k hk)
  ext x
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply]
  simp only [ShihIndex.leftHom, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  by_cases hx : x.val < (i.lowerPrefix hi).gap
  · have hupper : (k.succAbove x).val < i.gap := by
      have hgap := i.gap_lowerPrefix hi
      simp only [Fin.succAbove]
      split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ] <;> omega
    rw [dite_eq_left hx, dite_eq_left hupper]
    let x' : Fin (n + 1) := ⟨x.val, by
      have hindex := (i.lowerPrefix hi).p_add_q_add_gap
      omega⟩
    change (k.succAbove x).val =
      ((i.lowerPrefixFace k hk).succAbove x').val
    by_cases hxk : x.castSucc < k
    · have hxk' : x'.castSucc < i.lowerPrefixFace k hk := by
        simp only [Fin.lt_def, Fin.val_castSucc, x', ShihIndex.lowerPrefixFace]
        exact hxk
      rw [Fin.succAbove_of_castSucc_lt k x hxk,
        Fin.succAbove_of_castSucc_lt _ _ hxk']
      rfl
    · have hkx : k ≤ x.castSucc := le_of_not_gt hxk
      have hkx' : i.lowerPrefixFace k hk ≤ x'.castSucc := by
        simp only [Fin.le_def, Fin.val_castSucc, x', ShihIndex.lowerPrefixFace]
        exact hkx
      rw [Fin.succAbove_of_le_castSucc k x hkx,
        Fin.succAbove_of_le_castSucc _ _ hkx']
      rfl
  · have hupper : ¬(k.succAbove x).val < i.gap := by
      have hgap := i.gap_lowerPrefix hi
      have hkx : k ≤ x.castSucc := by
        simp only [Fin.le_def, Fin.val_castSucc]
        omega
      rw [Fin.succAbove_of_le_castSucc k x hkx]
      simp only [Fin.val_succ]
      omega
    rw [dite_eq_right hx, dite_eq_right hupper]
    have hkx : k ≤ x.castSucc := by
      simp only [Fin.le_def, Fin.val_castSucc]
      have hgap := i.gap_lowerPrefix hi
      omega
    have hsuffix :
        i.suffixInput x.succ (by
          simp only [Fin.val_succ]
          have hgap := i.gap_lowerPrefix hi
          omega) =
          (i.lowerPrefix hi).suffixInput x (by omega) := by
      apply Fin.ext
      simp only [ShihIndex.suffixInput, Fin.val_succ]
      have hgap := i.gap_lowerPrefix hi
      omega
    let y : Fin (n + 1) :=
      ⟨(i.lowerPrefix hi).gap - 1 +
          (i.lowerPrefix hi).shuffle.leftHom.toOrderHom
            ((i.lowerPrefix hi).suffixInput x (by omega)), by
        have hs := ((i.lowerPrefix hi).shuffle.leftHom.toOrderHom
          ((i.lowerPrefix hi).suffixInput x (by omega))).isLt
        change ((i.lowerPrefix hi).shuffle.leftHom.toOrderHom
          ((i.lowerPrefix hi).suffixInput x (by omega))).val <
            (i.lowerPrefix hi).p + 2 at hs
        have hindex := (i.lowerPrefix hi).p_add_q_add_gap
        change (i.lowerPrefix hi).gap - 1 +
          ((i.lowerPrefix hi).shuffle.leftHom.toOrderHom
            ((i.lowerPrefix hi).suffixInput x (by omega))).val < n + 1
        omega⟩
    have hky : i.lowerPrefixFace k hk ≤ y.castSucc := by
      change k.val ≤ (i.lowerPrefix hi).gap - 1 +
        ((i.lowerPrefix hi).shuffle.leftHom.toOrderHom
          ((i.lowerPrefix hi).suffixInput x (by omega))).val
      have hgap := i.gap_lowerPrefix hi
      have hlpos := (i.lowerPrefix hi).gap_pos
      omega
    simp only [Fin.succAbove_of_le_castSucc k x hkx]
    change i.gap - 1 +
      i.shuffle.leftHom.toOrderHom (i.suffixInput x.succ (by
        simp only [Fin.val_succ]
        have hgap := i.gap_lowerPrefix hi
        omega)) =
        ((i.lowerPrefixFace k hk).succAbove y).val
    rw [Fin.succAbove_of_le_castSucc _ _ hky]
    simp only [Fin.val_succ, y]
    rw [hsuffix]
    change i.gap - 1 +
      i.shuffle.leftHom.toOrderHom ((i.lowerPrefix hi).suffixInput x (by omega)) =
        (i.lowerPrefix hi).gap - 1 +
          i.shuffle.leftHom.toOrderHom ((i.lowerPrefix hi).suffixInput x (by omega)) + 1
    have hgap := i.gap_lowerPrefix hi
    have hlpos := (i.lowerPrefix hi).gap_pos
    omega

theorem delta_comp_rightHom_lowerPrefix {n : ℕ} (i : ShihIndex (n + 1))
    (k : Fin (n + 3)) (hk : k.val + 1 < i.gap) :
    SimplexCategory.δ k ≫ i.rightHom =
      (i.lowerPrefix (by omega)).rightHom ≫
        SimplexCategory.δ (i.lowerPrefixFace k hk) := by
  have hi : 1 < i.gap := by omega
  change SimplexCategory.δ k ≫ i.rightHom =
    (i.lowerPrefix hi).rightHom ≫ SimplexCategory.δ (i.lowerPrefixFace k hk)
  ext x
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply]
  simp only [ShihIndex.rightHom, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  by_cases hx : x.val < (i.lowerPrefix hi).gap
  · have hupper : (k.succAbove x).val < i.gap := by
      have hgap := i.gap_lowerPrefix hi
      simp only [Fin.succAbove]
      split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ] <;> omega
    rw [dite_eq_left hx, dite_eq_left hupper]
    let x' : Fin (n + 1) := ⟨x.val, by
      have hindex := (i.lowerPrefix hi).p_add_q_add_gap
      omega⟩
    change (k.succAbove x).val =
      ((i.lowerPrefixFace k hk).succAbove x').val
    by_cases hxk : x.castSucc < k
    · have hxk' : x'.castSucc < i.lowerPrefixFace k hk := by
        simp only [Fin.lt_def, Fin.val_castSucc, x', ShihIndex.lowerPrefixFace]
        exact hxk
      rw [Fin.succAbove_of_castSucc_lt k x hxk,
        Fin.succAbove_of_castSucc_lt _ _ hxk']
      rfl
    · have hkx : k ≤ x.castSucc := le_of_not_gt hxk
      have hkx' : i.lowerPrefixFace k hk ≤ x'.castSucc := by
        simp only [Fin.le_def, Fin.val_castSucc, x', ShihIndex.lowerPrefixFace]
        exact hkx
      rw [Fin.succAbove_of_le_castSucc k x hkx,
        Fin.succAbove_of_le_castSucc _ _ hkx']
      rfl
  · have hupper : ¬(k.succAbove x).val < i.gap := by
      have hgap := i.gap_lowerPrefix hi
      have hkx : k ≤ x.castSucc := by
        simp only [Fin.le_def, Fin.val_castSucc]
        omega
      rw [Fin.succAbove_of_le_castSucc k x hkx]
      simp only [Fin.val_succ]
      omega
    rw [dite_eq_right hx, dite_eq_right hupper]
    have hkx : k ≤ x.castSucc := by
      simp only [Fin.le_def, Fin.val_castSucc]
      have hgap := i.gap_lowerPrefix hi
      omega
    have hsuffix :
        i.suffixInput x.succ (by
          simp only [Fin.val_succ]
          have hgap := i.gap_lowerPrefix hi
          omega) =
          (i.lowerPrefix hi).suffixInput x (by omega) := by
      apply Fin.ext
      simp only [ShihIndex.suffixInput, Fin.val_succ]
      have hgap := i.gap_lowerPrefix hi
      omega
    let y : Fin (n + 1) :=
      ⟨(i.lowerPrefix hi).gap + (i.lowerPrefix hi).p +
          (i.lowerPrefix hi).shuffle.rightHom.toOrderHom
            ((i.lowerPrefix hi).suffixInput x (by omega)), by
        have hs := ((i.lowerPrefix hi).shuffle.rightHom.toOrderHom
          ((i.lowerPrefix hi).suffixInput x (by omega))).isLt
        change ((i.lowerPrefix hi).shuffle.rightHom.toOrderHom
          ((i.lowerPrefix hi).suffixInput x (by omega))).val <
            (i.lowerPrefix hi).q + 1 at hs
        have hindex := (i.lowerPrefix hi).p_add_q_add_gap
        change (i.lowerPrefix hi).gap + (i.lowerPrefix hi).p +
          ((i.lowerPrefix hi).shuffle.rightHom.toOrderHom
            ((i.lowerPrefix hi).suffixInput x (by omega))).val < n + 1
        omega⟩
    have hky : i.lowerPrefixFace k hk ≤ y.castSucc := by
      change k.val ≤ (i.lowerPrefix hi).gap + (i.lowerPrefix hi).p +
        ((i.lowerPrefix hi).shuffle.rightHom.toOrderHom
          ((i.lowerPrefix hi).suffixInput x (by omega))).val
      have hgap := i.gap_lowerPrefix hi
      omega
    simp only [Fin.succAbove_of_le_castSucc k x hkx]
    change i.gap + i.p +
      i.shuffle.rightHom.toOrderHom (i.suffixInput x.succ (by
        simp only [Fin.val_succ]
        have hgap := i.gap_lowerPrefix hi
        omega)) =
        ((i.lowerPrefixFace k hk).succAbove y).val
    rw [Fin.succAbove_of_le_castSucc _ _ hky]
    simp only [Fin.val_succ, y]
    rw [hsuffix]
    change i.gap + i.p +
      i.shuffle.rightHom.toOrderHom ((i.lowerPrefix hi).suffixInput x (by omega)) =
        (i.lowerPrefix hi).gap + i.p +
          i.shuffle.rightHom.toOrderHom ((i.lowerPrefix hi).suffixInput x (by omega)) + 1
    have hgap := i.gap_lowerPrefix hi
    omega

theorem map_leftHom_comp_delta_lowerPrefix {C : Type u} [Category.{v} C]
    (X : SimplicialObject C) {n : ℕ} (i : ShihIndex (n + 1))
    (k : Fin (n + 3)) (hk : k.val + 1 < i.gap) :
    X.map i.leftHom.op ≫ X.δ k =
      X.δ (i.lowerPrefixFace k hk) ≫
        X.map (i.lowerPrefix (by omega)).leftHom.op := by
  simpa [SimplicialObject.δ] using congrArg (fun f => X.map f.op)
    (delta_comp_leftHom_lowerPrefix i k hk)

theorem map_rightHom_comp_delta_lowerPrefix {C : Type u} [Category.{v} C]
    (X : SimplicialObject C) {n : ℕ} (i : ShihIndex (n + 1))
    (k : Fin (n + 3)) (hk : k.val + 1 < i.gap) :
    X.map i.rightHom.op ≫ X.δ k =
      X.δ (i.lowerPrefixFace k hk) ≫
        X.map (i.lowerPrefix (by omega)).rightHom.op := by
  simpa [SimplicialObject.δ] using congrArg (fun f => X.map f.op)
    (delta_comp_rightHom_lowerPrefix i k hk)

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- A paired upper/lower prefix-face contribution cancels pointwise. -/
theorem shihPrefixBoundaryTerm_add_eq_zero (X Y : SimplicialObject C) {n : ℕ}
    (i : ShihIndex (n + 1)) (k : Fin (n + 3)) (hk : k.val + 1 < i.gap) :
    shihUpperBoundaryTerm X Y (n + 1) i k +
      shihLowerBoundaryTerm X Y n (i.lowerPrefixFace k hk)
        (i.lowerPrefix (by omega)) = 0 := by
  unfold shihUpperBoundaryTerm shihLowerBoundaryTerm shihSummand
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    MonoidalCategory.tensorHom_comp_tensorHom]
  rw [map_leftHom_comp_delta_lowerPrefix X i k hk,
    map_rightHom_comp_delta_lowerPrefix Y i k hk,
    ShihIndex.sign_lowerPrefix]
  simp only [ShihIndex.lowerPrefixFace, neg_smul, smul_neg, add_neg_cancel]

/-- The upper and lower Shih boundary terms whose face is strictly before the
active block cancel after the canonical prefix-removal reindexing. -/
theorem shihPrefixBoundary_sum_eq_zero (X Y : SimplicialObject C) (n : ℕ) :
    (∑ z : ShihUpperPrefixIndex n,
        shihUpperBoundaryTerm X Y (n + 1) z.val.2 z.val.1) +
      ∑ z : ShihLowerPrefixIndex n,
        shihLowerBoundaryTerm X Y n z.val.2 z.val.1 = 0 := by
  rw [← (shihUpperPrefixEquivLowerPrefix n).sum_comp (fun z =>
    shihLowerBoundaryTerm X Y n z.val.2 z.val.1)]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun z _ =>
    shihPrefixBoundaryTerm_add_eq_zero X Y z.val.2 z.val.1 z.property

end AlgebraicTopology.EilenbergZilber
