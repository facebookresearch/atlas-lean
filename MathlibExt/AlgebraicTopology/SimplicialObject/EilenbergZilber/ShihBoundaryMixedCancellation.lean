/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryPrefixCancellation
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleMixedFace

/-!
# Mixed active-face cancellation in the Shih boundary

This file treats the active Shih faces corresponding to mixed shuffle
boundaries.  Swapping the adjacent mixed positions preserves both simplex
words and reverses the shuffle sign.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

namespace ShihIndex

/-- Replace only the shuffle carried by a Shih index. -/
def replaceShuffle {n : ℕ} (i : ShihIndex n)
    (s : Shuffle (i.p + 1) i.q) : ShihIndex n where
  p := i.p
  q := i.q
  shuffle := s

@[simp]
theorem gap_replaceShuffle {n : ℕ} (i : ShihIndex n)
    (s : Shuffle (i.p + 1) i.q) :
    (i.replaceShuffle s).gap = i.gap := rfl

/-- The global face obtained from a boundary face of the active shuffle
block. -/
def activeBoundaryFace {n : ℕ} (i : ShihIndex n)
    (r : Fin (i.p + 1 + i.q + 1)) : Fin (n + 2) :=
  ⟨i.gap + r.val, by
    have hi := i.p_add_q_add_gap
    omega⟩

@[simp]
theorem activeBoundaryFace_replaceShuffle {n : ℕ} (i : ShihIndex n)
    (s : Shuffle (i.p + 1) i.q) (r : Fin (i.p + 1 + i.q + 1)) :
    (i.replaceShuffle s).activeBoundaryFace r = i.activeBoundaryFace r := by
  apply Fin.ext
  rfl

/-- Local suffix coordinate before deleting an active boundary face. -/
def activeInput {n : ℕ} (i : ShihIndex n) (k : Fin (n + 1))
    (hk : i.gap ≤ k.val) : Fin (i.p + 1 + i.q) :=
  ⟨k.val - i.gap, by
    have hi := i.p_add_q_add_gap
    have hk' := k.isLt
    omega⟩

theorem suffixInput_activeBoundaryFace_succAbove {n : ℕ} (i : ShihIndex n)
    (r : Fin (i.p + 1 + i.q + 1)) (k : Fin (n + 1))
    (hk : i.gap ≤ k.val) :
    i.suffixInput ((i.activeBoundaryFace r).succAbove k) (by
      by_cases hkr : k.castSucc < i.activeBoundaryFace r
      · rw [Fin.succAbove_of_castSucc_lt _ _ hkr]
        simp only [Fin.val_castSucc]
        exact hk
      · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hkr)]
        simp only [Fin.val_succ]
        omega) =
      r.succAbove (i.activeInput k hk) := by
  apply Fin.ext
  change ((i.activeBoundaryFace r).succAbove k).val - i.gap =
    (r.succAbove (i.activeInput k hk)).val
  by_cases hkr : k.castSucc < i.activeBoundaryFace r
  · have hlocal : (i.activeInput k hk).castSucc < r := by
      simp only [Fin.lt_def, Fin.val_castSucc, activeInput]
      simp only [Fin.lt_def, Fin.val_castSucc, activeBoundaryFace] at hkr
      omega
    rw [Fin.succAbove_of_castSucc_lt _ _ hkr,
      Fin.succAbove_of_castSucc_lt _ _ hlocal]
    simp only [activeInput, Fin.val_castSucc]
  · have hlocal : r ≤ (i.activeInput k hk).castSucc := by
      simp only [Fin.le_def, Fin.val_castSucc, activeInput]
      simp only [Fin.lt_def, Fin.val_castSucc, activeBoundaryFace] at hkr
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hkr),
      Fin.succAbove_of_le_castSucc _ _ hlocal]
    simp only [activeInput, Fin.val_succ]
    omega

theorem sign_replaceShuffle_partner {n : ℕ} (i : ShihIndex n)
    (x : Shuffle.MixedFace (i.p + 1) i.q) (hx : x.shuffle = i.shuffle) :
    (i.replaceShuffle x.partner.shuffle).sign = -i.sign := by
  change (-1 : ℤ) ^ (i.gap + 1) * shuffleSignZ x.partner.shuffle =
    -((-1 : ℤ) ^ (i.gap + 1) * shuffleSignZ i.shuffle)
  rw [x.shuffleSignZ_partner, hx]
  ring

/-- A Shih index with prescribed positive gap and shuffle. -/
def ofGap (p q m : ℕ) (hm : 0 < m) (s : Shuffle (p + 1) q) :
    ShihIndex (p + q + m) where
  p := ⟨p, by omega⟩
  q := ⟨q, by
    change q < p + q + m - p
    omega⟩
  shuffle := s

@[simp]
theorem gap_ofGap (p q m : ℕ) (hm : 0 < m) (s : Shuffle (p + 1) q) :
    (ofGap p q m hm s).gap = m := by
  simp only [ofGap, gap]
  omega

@[simp]
theorem ofGap_replaceShuffle (p q m : ℕ) (hm : 0 < m)
    (s t : Shuffle (p + 1) q) :
    (ofGap p q m hm s).replaceShuffle t = ofGap p q m hm t := by
  rfl

/-- The active boundary face with the ambient degree displayed explicitly. -/
def activeBoundaryFaceOfGap (p q m : ℕ) (_hm : 0 < m)
    (r : Fin (p + 1 + q + 1)) : Fin (p + q + m + 2) :=
  ⟨m + r.val, by omega⟩

@[simp]
theorem activeBoundaryFace_ofGap (p q m : ℕ) (hm : 0 < m)
    (s : Shuffle (p + 1) q) (r : Fin (p + 1 + q + 1)) :
    (ofGap p q m hm s).activeBoundaryFace r =
      activeBoundaryFaceOfGap p q m hm r := by
  apply Fin.ext
  simp only [activeBoundaryFace, activeBoundaryFaceOfGap, gap_ofGap]

end ShihIndex

theorem delta_activeBoundaryFace_comp_leftHom_partner {n : ℕ}
    (i : ShihIndex n) (x : Shuffle.MixedFace (i.p + 1) i.q)
    (hx : x.shuffle = i.shuffle) :
    SimplexCategory.δ (i.activeBoundaryFace x.faceIndex) ≫ i.leftHom =
      SimplexCategory.δ (i.activeBoundaryFace x.partner.faceIndex) ≫
        (i.replaceShuffle x.partner.shuffle).leftHom := by
  simp only [Shuffle.MixedFace.partner_faceIndex]
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply]
  simp only [ShihIndex.leftHom, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  by_cases hk : k.val < i.gap
  · have hleft :
        ((i.activeBoundaryFace x.faceIndex).succAbove k).val < i.gap := by
      have hkface : k.castSucc < i.activeBoundaryFace x.faceIndex := by
        simp only [Fin.lt_def, Fin.val_castSucc, ShihIndex.activeBoundaryFace]
        omega
      rw [Fin.succAbove_of_castSucc_lt _ _ hkface]
      simpa only [Fin.val_castSucc] using hk
    have hright :
        ((i.activeBoundaryFace x.faceIndex).succAbove k).val <
            (i.replaceShuffle x.partner.shuffle).gap := by
      simpa only [ShihIndex.gap_replaceShuffle] using hleft
    rw [dite_eq_left hleft, dite_eq_left hright]
  · have hleft : ¬
        ((i.activeBoundaryFace x.faceIndex).succAbove k).val < i.gap := by
      by_cases hkface : k.castSucc < i.activeBoundaryFace x.faceIndex
      · rw [Fin.succAbove_of_castSucc_lt _ _ hkface]
        simp only [Fin.val_castSucc]
        omega
      · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hkface)]
        simp only [Fin.val_succ]
        omega
    have hright : ¬
        ((i.activeBoundaryFace x.faceIndex).succAbove k).val <
            (i.replaceShuffle x.partner.shuffle).gap := by
      simp only [ShihIndex.gap_replaceShuffle]
      exact hleft
    rw [dite_eq_right hleft, dite_eq_right hright]
    change i.gap - 1 +
      i.shuffle.leftHom.toOrderHom
        (i.suffixInput ((i.activeBoundaryFace x.faceIndex).succAbove k) (by omega)) =
      i.gap - 1 + x.partner.shuffle.leftHom.toOrderHom
        (i.suffixInput ((i.activeBoundaryFace x.faceIndex).succAbove k) (by omega))
    have hsuffix := i.suffixInput_activeBoundaryFace_succAbove
      x.faceIndex k (by omega)
    rw [hsuffix]
    rw [← hx]
    have hshuffle := congrArg Fin.val
      (x.leftHom_partner_succAbove (i.activeInput k (by omega)))
    omega

theorem delta_activeBoundaryFace_comp_rightHom_partner {n : ℕ}
    (i : ShihIndex n) (x : Shuffle.MixedFace (i.p + 1) i.q)
    (hx : x.shuffle = i.shuffle) :
    SimplexCategory.δ (i.activeBoundaryFace x.faceIndex) ≫ i.rightHom =
      SimplexCategory.δ (i.activeBoundaryFace x.partner.faceIndex) ≫
        (i.replaceShuffle x.partner.shuffle).rightHom := by
  simp only [Shuffle.MixedFace.partner_faceIndex]
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply]
  simp only [ShihIndex.rightHom, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  by_cases hk : k.val < i.gap
  · have hleft :
        ((i.activeBoundaryFace x.faceIndex).succAbove k).val < i.gap := by
      have hkface : k.castSucc < i.activeBoundaryFace x.faceIndex := by
        simp only [Fin.lt_def, Fin.val_castSucc, ShihIndex.activeBoundaryFace]
        omega
      rw [Fin.succAbove_of_castSucc_lt _ _ hkface]
      simpa only [Fin.val_castSucc] using hk
    have hright :
        ((i.activeBoundaryFace x.faceIndex).succAbove k).val <
            (i.replaceShuffle x.partner.shuffle).gap := by
      simpa only [ShihIndex.gap_replaceShuffle] using hleft
    rw [dite_eq_left hleft, dite_eq_left hright]
  · have hleft : ¬
        ((i.activeBoundaryFace x.faceIndex).succAbove k).val < i.gap := by
      by_cases hkface : k.castSucc < i.activeBoundaryFace x.faceIndex
      · rw [Fin.succAbove_of_castSucc_lt _ _ hkface]
        simp only [Fin.val_castSucc]
        omega
      · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hkface)]
        simp only [Fin.val_succ]
        omega
    have hright : ¬
        ((i.activeBoundaryFace x.faceIndex).succAbove k).val <
            (i.replaceShuffle x.partner.shuffle).gap := by
      simp only [ShihIndex.gap_replaceShuffle]
      exact hleft
    rw [dite_eq_right hleft, dite_eq_right hright]
    change i.gap + i.p +
      i.shuffle.rightHom.toOrderHom
        (i.suffixInput ((i.activeBoundaryFace x.faceIndex).succAbove k) (by omega)) =
      i.gap + i.p + x.partner.shuffle.rightHom.toOrderHom
        (i.suffixInput ((i.activeBoundaryFace x.faceIndex).succAbove k) (by omega))
    have hsuffix := i.suffixInput_activeBoundaryFace_succAbove
      x.faceIndex k (by omega)
    rw [hsuffix]
    rw [← hx]
    have hshuffle := congrArg Fin.val
      (x.rightHom_partner_succAbove (i.activeInput k (by omega)))
    omega

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- Mixed active boundary faces cancel pointwise under the adjacent-position
partner involution. -/
theorem shihMixedActiveBoundaryTerm_add_partner_eq_zero
    (X Y : SimplicialObject C) {n : ℕ} (i : ShihIndex n)
    (x : Shuffle.MixedFace (i.p + 1) i.q) (hx : x.shuffle = i.shuffle) :
    shihUpperBoundaryTerm X Y n i (i.activeBoundaryFace x.faceIndex) +
      shihUpperBoundaryTerm X Y n
        (i.replaceShuffle x.partner.shuffle)
        (i.activeBoundaryFace x.partner.faceIndex) = 0 := by
  unfold shihUpperBoundaryTerm shihSummand
  simp only [Preadditive.zsmul_comp,
    MonoidalCategory.tensorHom_comp_tensorHom]
  have hleftX :
      X.map i.leftHom.op ≫ X.δ (i.activeBoundaryFace x.faceIndex) =
        X.map (i.replaceShuffle x.partner.shuffle).leftHom.op ≫
          X.δ (i.activeBoundaryFace x.partner.faceIndex) := by
    simpa [SimplicialObject.δ] using congrArg (fun f => X.map f.op)
      (delta_activeBoundaryFace_comp_leftHom_partner i x hx)
  have hrightY :
      Y.map i.rightHom.op ≫ Y.δ (i.activeBoundaryFace x.faceIndex) =
        Y.map (i.replaceShuffle x.partner.shuffle).rightHom.op ≫
          Y.δ (i.activeBoundaryFace x.partner.faceIndex) := by
    simpa [SimplicialObject.δ] using congrArg (fun f => Y.map f.op)
      (delta_activeBoundaryFace_comp_rightHom_partner i x hx)
  rw [hleftX, hrightY, i.sign_replaceShuffle_partner x hx]
  simp only [ShihIndex.activeBoundaryFace, Shuffle.MixedFace.partner_faceIndex,
    neg_smul, smul_neg, add_neg_cancel]

/-- For fixed bidegree and positive gap, all mixed active boundary faces cancel
in the finite sum. -/
theorem shihMixedActiveBoundary_sum_eq_zero
    (X Y : SimplicialObject C) (p q m : ℕ) (hm : 0 < m) :
    ∑ x : Shuffle.MixedFace (p + 1) q,
      shihUpperBoundaryTerm X Y (p + q + m)
        (ShihIndex.ofGap p q m hm x.shuffle)
        (ShihIndex.activeBoundaryFaceOfGap p q m hm x.faceIndex) = 0 := by
  apply Finset.sum_involution (fun x _ => x.partner)
  · intro x _
    have hcancel := shihMixedActiveBoundaryTerm_add_partner_eq_zero X Y
      (ShihIndex.ofGap p q m hm x.shuffle) x rfl
    have hindex :
        (ShihIndex.ofGap p q m hm x.shuffle).replaceShuffle
            x.partner.shuffle =
          ShihIndex.ofGap p q m hm x.partner.shuffle := by
      rfl
    have hfirst :
        (ShihIndex.ofGap p q m hm x.shuffle).activeBoundaryFace x.faceIndex =
          ShihIndex.activeBoundaryFaceOfGap p q m hm x.faceIndex := by
      exact ShihIndex.activeBoundaryFace_ofGap p q m hm x.shuffle x.faceIndex
    have hsecond :
        shihUpperBoundaryTerm X Y (p + q + m)
            ((ShihIndex.ofGap p q m hm x.shuffle).replaceShuffle
              x.partner.shuffle)
            ((ShihIndex.ofGap p q m hm x.shuffle).activeBoundaryFace
              x.partner.faceIndex) =
          shihUpperBoundaryTerm X Y (p + q + m)
            (ShihIndex.ofGap p q m hm x.partner.shuffle)
            (ShihIndex.activeBoundaryFaceOfGap p q m hm
              x.partner.faceIndex) := by
      rw [hindex]
      congr 1
    calc
      _ = shihUpperBoundaryTerm X Y (p + q + m)
            (ShihIndex.ofGap p q m hm x.shuffle)
            ((ShihIndex.ofGap p q m hm x.shuffle).activeBoundaryFace
              x.faceIndex) +
          shihUpperBoundaryTerm X Y (p + q + m)
            ((ShihIndex.ofGap p q m hm x.shuffle).replaceShuffle
              x.partner.shuffle)
            ((ShihIndex.ofGap p q m hm x.shuffle).activeBoundaryFace
              x.partner.faceIndex) := by rw [hfirst, hsecond]
      _ = 0 := hcancel
  · intro x _ _
    exact x.partner_ne
  · intro x _
    simp
  · intro x _
    simp

end AlgebraicTopology.EilenbergZilber
