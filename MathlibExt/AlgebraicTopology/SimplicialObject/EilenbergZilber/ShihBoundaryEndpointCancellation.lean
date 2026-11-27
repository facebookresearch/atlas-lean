/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryNonmixedCancellation

/-!
# Endpoint cancellation in the active Shih boundary

The nonmixed active boundary has two exceptional endpoint interactions.  A
left insertion at zero cancels the face immediately preceding the active
block, while a left insertion at the final position cancels a right insertion
at zero.  The identity and zero-cut terms are the only endpoints not covered
by these two families.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

namespace ShihIndex

/-- The face immediately preceding the active shuffle block. -/
def transitionUpperFace (p q m : ℕ) : Fin (p + q + m + 3) :=
  ⟨m, by omega⟩

@[simp]
theorem leftBoundaryUpperFace_zero (p q m : ℕ)
    (t : Shuffle (p + 1) q) :
    leftBoundaryUpperFace p q m t 0 = transitionUpperFace p q m := by
  apply Fin.ext
  simp [leftBoundaryUpperFace, transitionUpperFace,
    Shuffle.leftBoundaryIndex_zero]

@[simp]
theorem rightBoundaryUpperFace_zero (p q m : ℕ)
    (t : Shuffle (p + 1) q) :
    rightBoundaryUpperFace p q m t 0 = transitionUpperFace p q m := by
  apply Fin.ext
  simp [rightBoundaryUpperFace, transitionUpperFace,
    Shuffle.rightBoundaryIndex_zero]

@[simp]
theorem leftBoundaryUpperFace_last (p q m : ℕ)
    (t : Shuffle (p + 1) q) :
    leftBoundaryUpperFace p q m t (Fin.last (p + 2)) =
      Fin.last (p + q + m + 2) := by
  apply Fin.ext
  simp [leftBoundaryUpperFace, Shuffle.leftBoundaryIndex_last]
  omega

/-- The transition-face coefficient is opposite to the coefficient of the
zero left insertion one gap lower. -/
theorem transitionCoefficient_add_leftZero_eq_zero
    (p q m : ℕ) (hm : 0 < m) (t : Shuffle (p + 1) q) :
    ((-1 : ℤ) ^ (transitionUpperFace p q m).val) *
          (ofGap p q (m + 1) (by omega) t).sign +
        leftUpperCoefficient p q m hm t 0 = 0 := by
  unfold transitionUpperFace leftUpperCoefficient leftBoundaryUpperFace
  rw [sign_ofGap, sign_leftBoundaryUpperIndex]
  simp only [Shuffle.leftBoundaryIndex_zero, Fin.val_zero, Nat.add_zero]
  have hs := Shuffle.shuffleSignZ_leftBoundaryShuffle t (0 : Fin (p + 3))
  simp only [Shuffle.leftBoundaryIndex_zero, Fin.val_zero, pow_zero,
    one_mul] at hs
  rw [hs]
  have hparity :
      (-1 : ℤ) ^ m * (-1 : ℤ) ^ (m + 1) = -1 := by
    rw [← pow_add]
    have h : m + (m + 1) = 2 * m + 1 := by omega
    rw [h, pow_succ, pow_mul]
    norm_num
  rw [show m + 1 + 1 = m + 2 by omega, pow_add]
  calc
    _ = ((-1 : ℤ) ^ m * (-1 : ℤ) ^ (m + 1)) *
          ((-1 : ℤ) * shuffleSignZ t) +
        ((-1 : ℤ) ^ m * (-1 : ℤ) ^ (m + 1)) *
          shuffleSignZ t := by ring
    _ = 0 := by rw [hparity]; ring

/-- The final left-insertion coefficient is opposite to the zero
right-insertion coefficient. -/
theorem leftLastCoefficient_add_rightZero_eq_zero
    (p q m : ℕ) (hm : 0 < m) (t : Shuffle (p + 1) q) :
    leftUpperCoefficient p q m hm t (Fin.last (p + 2)) +
        rightUpperCoefficient p q m hm t 0 = 0 := by
  unfold leftUpperCoefficient rightUpperCoefficient leftBoundaryUpperFace
    rightBoundaryUpperFace
  rw [sign_leftBoundaryUpperIndex, sign_rightBoundaryUpperIndex]
  simp only [Shuffle.leftBoundaryIndex_last,
    Shuffle.rightBoundaryIndex_zero, Fin.val_last, Fin.val_zero, Nat.add_zero]
  have hsLeft := Shuffle.shuffleSignZ_leftBoundaryShuffle t (Fin.last (p + 2))
  simp only [Shuffle.leftBoundaryIndex_last, Fin.val_last] at hsLeft
  have hsRight := Shuffle.shuffleSignZ_rightBoundaryShuffle t (0 : Fin (q + 2))
  simp only [Shuffle.rightBoundaryIndex_zero, Fin.val_zero, pow_zero,
    one_mul] at hsRight
  have hleft :
      (-1 : ℤ) ^ (m + (p + 1 + 1 + q)) *
          ((-1 : ℤ) ^ (m + 1) *
            shuffleSignZ (Shuffle.leftBoundaryShuffle t (Fin.last (p + 2)))) =
        ((-1 : ℤ) ^ m * (-1 : ℤ) ^ (m + 1)) *
          ((-1 : ℤ) ^ (p + 2) * shuffleSignZ t) := by
    rw [pow_add]
    rw [show p + 1 + 1 + q = p + 2 + q by omega]
    calc
      _ = ((-1 : ℤ) ^ m * (-1 : ℤ) ^ (m + 1)) *
          ((-1 : ℤ) ^ (p + 2 + q) *
            shuffleSignZ (Shuffle.leftBoundaryShuffle t (Fin.last (p + 2)))) := by ring
      _ = _ := by rw [hsLeft]
  have hright :
      (-1 : ℤ) ^ m *
          ((-1 : ℤ) ^ (m + 1) *
            shuffleSignZ (Shuffle.rightBoundaryShuffle t 0)) =
        ((-1 : ℤ) ^ m * (-1 : ℤ) ^ (m + 1)) *
          ((-1 : ℤ) ^ (p + 1) * shuffleSignZ t) := by
    rw [hsRight]
    ring
  rw [hleft, hright]
  have hparity :
      (-1 : ℤ) ^ m * (-1 : ℤ) ^ (m + 1) = -1 := by
    rw [← pow_add]
    have h : m + (m + 1) = 2 * m + 1 := by omega
    rw [h, pow_succ, pow_mul]
    norm_num
  rw [hparity]
  rw [show p + 2 = (p + 1) + 1 by omega, pow_succ]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Deleting the zero left insertion gives the same left simplex word as
deleting the transition vertex from the index with one longer prefix. -/
theorem delta_transition_comp_leftHom_eq_leftZero
    (p q m : ℕ) (hm : 0 < m) (t : Shuffle (p + 1) q) :
    SimplexCategory.δ (transitionUpperFace p q m) ≫
        (ofGap p q (m + 1) (by omega) t).leftHom =
      SimplexCategory.δ (leftBoundaryUpperFace p q m t 0) ≫
        (leftBoundaryUpperIndex p q m hm t 0).leftHom := by
  rw [leftBoundaryUpperFace_zero]
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext x
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, leftHom, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
    gap_ofGap, gap_leftBoundaryUpperIndex]
  change
    (if _h : ((transitionUpperFace p q m).succAbove x).val < m + 1 then _ else _) =
      (if _h : ((transitionUpperFace p q m).succAbove x).val < m then _ else _)
  by_cases hx : x.val < m
  · have hface : x.castSucc < transitionUpperFace p q m := by
      simpa [Fin.lt_def, transitionUpperFace] using hx
    have hy : ((transitionUpperFace p q m).succAbove x).val < m := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hface]
      simpa only [Fin.val_castSucc] using hx
    rw [dite_eq_left (by omega), dite_eq_left hy]
  · have hface : transitionUpperFace p q m ≤ x.castSucc := by
      simpa [Fin.le_def, transitionUpperFace] using le_of_not_gt hx
    have hxm : m ≤ x.val := le_of_not_gt hx
    have hy : ((transitionUpperFace p q m).succAbove x).val = x.val + 1 := by
      rw [Fin.succAbove_of_le_castSucc _ _ hface]
      rfl
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]
    apply Fin.ext
    let z : Fin (p + 1 + q + 1) :=
      ⟨x.val - m, by
        have hxlt := x.isLt
        omega⟩
    have hsuffixRaised :
        (ofGap p q (m + 1) (by omega) t).suffixInput
            ((transitionUpperFace p q m).succAbove x) (by
              rw [gap_ofGap]
              omega) = z := by
      apply Fin.ext
      simp [suffixInput, hy, z]
    have hsuffixLeft :
        (leftBoundaryUpperIndex p q m hm t 0).suffixInput
            ((transitionUpperFace p q m).succAbove x) (by
              rw [gap_leftBoundaryUpperIndex]
              omega) =
          (Shuffle.leftBoundaryIndex t 0).succAbove (Fin.cast (by omega) z) := by
      apply Fin.ext
      simp only [suffixInput, hy, z, Shuffle.leftBoundaryIndex_zero,
        Fin.zero_succAbove, Fin.val_succ, Fin.val_cast]
      rw [gap_leftBoundaryUpperIndex]
      rw [Nat.add_comm x.val 1, Nat.add_sub_assoc hxm,
        Nat.add_comm 1 (x.val - m)]
    change m + 1 - 1 +
        (t.leftHom.toOrderHom
          ((ofGap p q (m + 1) (by omega) t).suffixInput
            ((transitionUpperFace p q m).succAbove x) (by
              rw [gap_ofGap]
              omega))).val =
      m - 1 +
        ((Shuffle.leftBoundaryShuffle t 0).leftHom.toOrderHom
          ((leftBoundaryUpperIndex p q m hm t 0).suffixInput
            ((transitionUpperFace p q m).succAbove x) (by
              rw [gap_leftBoundaryUpperIndex]
              omega))).val
    rw [hsuffixRaised, hsuffixLeft]
    have hshuffle := Shuffle.leftHom_leftBoundaryShuffle_succAbove
      t (0 : Fin (p + 3)) z
    have hval := congrArg Fin.val hshuffle
    rw [hval]
    simp only [Fin.zero_succAbove, Fin.val_succ]
    omega

set_option backward.isDefEq.respectTransparency false in
/-- Right-factor version of `delta_transition_comp_leftHom_eq_leftZero`. -/
theorem delta_transition_comp_rightHom_eq_leftZero
    (p q m : ℕ) (hm : 0 < m) (t : Shuffle (p + 1) q) :
    SimplexCategory.δ (transitionUpperFace p q m) ≫
        (ofGap p q (m + 1) (by omega) t).rightHom =
      SimplexCategory.δ (leftBoundaryUpperFace p q m t 0) ≫
        (leftBoundaryUpperIndex p q m hm t 0).rightHom := by
  rw [leftBoundaryUpperFace_zero]
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext x
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, rightHom, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
    gap_ofGap, gap_leftBoundaryUpperIndex]
  change
    (if _h : ((transitionUpperFace p q m).succAbove x).val < m + 1 then _ else _) =
      (if _h : ((transitionUpperFace p q m).succAbove x).val < m then _ else _)
  by_cases hx : x.val < m
  · have hface : x.castSucc < transitionUpperFace p q m := by
      simpa [Fin.lt_def, transitionUpperFace] using hx
    have hy : ((transitionUpperFace p q m).succAbove x).val < m := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hface]
      simpa only [Fin.val_castSucc] using hx
    rw [dite_eq_left (by omega), dite_eq_left hy]
  · have hface : transitionUpperFace p q m ≤ x.castSucc := by
      simpa [Fin.le_def, transitionUpperFace] using le_of_not_gt hx
    have hxm : m ≤ x.val := le_of_not_gt hx
    have hy : ((transitionUpperFace p q m).succAbove x).val = x.val + 1 := by
      rw [Fin.succAbove_of_le_castSucc _ _ hface]
      rfl
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]
    apply Fin.ext
    let z : Fin (p + 1 + q + 1) :=
      ⟨x.val - m, by
        have hxlt := x.isLt
        omega⟩
    have hsuffixRaised :
        (ofGap p q (m + 1) (by omega) t).suffixInput
            ((transitionUpperFace p q m).succAbove x) (by
              rw [gap_ofGap]
              omega) = z := by
      apply Fin.ext
      simp [suffixInput, hy, z]
    have hsuffixLeft :
        (leftBoundaryUpperIndex p q m hm t 0).suffixInput
            ((transitionUpperFace p q m).succAbove x) (by
              rw [gap_leftBoundaryUpperIndex]
              omega) =
          (Shuffle.leftBoundaryIndex t 0).succAbove (Fin.cast (by omega) z) := by
      apply Fin.ext
      simp only [suffixInput, hy, z, Shuffle.leftBoundaryIndex_zero,
        Fin.zero_succAbove, Fin.val_succ, Fin.val_cast]
      rw [gap_leftBoundaryUpperIndex]
      rw [Nat.add_comm x.val 1, Nat.add_sub_assoc hxm,
        Nat.add_comm 1 (x.val - m)]
    change m + 1 + p +
        (t.rightHom.toOrderHom
          ((ofGap p q (m + 1) (by omega) t).suffixInput
            ((transitionUpperFace p q m).succAbove x) (by
              rw [gap_ofGap]
              omega))).val =
      m + (p + 1) +
        ((Shuffle.leftBoundaryShuffle t 0).rightHom.toOrderHom
          ((leftBoundaryUpperIndex p q m hm t 0).suffixInput
            ((transitionUpperFace p q m).succAbove x) (by
              rw [gap_leftBoundaryUpperIndex]
              omega))).val
    rw [hsuffixRaised, hsuffixLeft]
    have hshuffle := Shuffle.rightHom_leftBoundaryShuffle_succAbove
      t (0 : Fin (p + 3)) z
    have hval := congrArg Fin.val hshuffle
    rw [hval]
    omega

set_option backward.isDefEq.respectTransparency false in
/-- The final left insertion and the zero right insertion have the same left
simplex word after their respective active face is deleted. -/
theorem delta_leftLast_comp_leftHom_eq_rightZero
    (p q m : ℕ) (hm : 0 < m) (t : Shuffle (p + 1) q) :
    SimplexCategory.δ
          (leftBoundaryUpperFace p q m t (Fin.last (p + 2))) ≫
        (leftBoundaryUpperIndex p q m hm t (Fin.last (p + 2))).leftHom =
      SimplexCategory.δ (rightBoundaryUpperFace p q m t 0) ≫
        (rightBoundaryUpperIndex p q m hm t 0).leftHom := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext x
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, leftHom, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
    gap_leftBoundaryUpperIndex, gap_rightBoundaryUpperIndex]
  change
    (if _h :
        ((leftBoundaryUpperFace p q m t (Fin.last (p + 2))).succAbove x).val < m
      then _ else _) =
      (if _h : ((rightBoundaryUpperFace p q m t 0).succAbove x).val < m
        then _ else _)
  by_cases hx : x.val < m
  · have hleftFace :
        x.castSucc < leftBoundaryUpperFace p q m t (Fin.last (p + 2)) := by
      rw [leftBoundaryUpperFace_last]
      exact Fin.castSucc_lt_last x
    have hrightFace : x.castSucc < rightBoundaryUpperFace p q m t 0 := by
      rw [rightBoundaryUpperFace_zero]
      simpa [Fin.lt_def, transitionUpperFace] using hx
    have hleft :
        ((leftBoundaryUpperFace p q m t (Fin.last (p + 2))).succAbove x).val < m := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hleftFace]
      simpa only [Fin.val_castSucc] using hx
    have hright :
        ((rightBoundaryUpperFace p q m t 0).succAbove x).val < m := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hrightFace]
      simpa only [Fin.val_castSucc] using hx
    rw [dite_eq_left hleft, dite_eq_left hright]
    apply Fin.ext
    change
      ((leftBoundaryUpperFace p q m t (Fin.last (p + 2))).succAbove x).val =
        ((rightBoundaryUpperFace p q m t 0).succAbove x).val
    rw [Fin.succAbove_of_castSucc_lt _ _ hleftFace,
      Fin.succAbove_of_castSucc_lt _ _ hrightFace]
  · have hxm : m ≤ x.val := le_of_not_gt hx
    have hleftFace :
        x.castSucc < leftBoundaryUpperFace p q m t (Fin.last (p + 2)) := by
      rw [leftBoundaryUpperFace_last]
      exact Fin.castSucc_lt_last x
    have hrightFace : rightBoundaryUpperFace p q m t 0 ≤ x.castSucc := by
      rw [rightBoundaryUpperFace_zero]
      simpa [Fin.le_def, transitionUpperFace] using hxm
    have hleftVal :
        ((leftBoundaryUpperFace p q m t (Fin.last (p + 2))).succAbove x).val =
          x.val := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hleftFace]
      rfl
    have hrightVal :
        ((rightBoundaryUpperFace p q m t 0).succAbove x).val = x.val + 1 := by
      rw [Fin.succAbove_of_le_castSucc _ _ hrightFace]
      rfl
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]
    apply Fin.ext
    let z : Fin (p + 1 + q + 1) :=
      ⟨x.val - m, by
        have hxlt := x.isLt
        omega⟩
    have hsuffixLeft :
        (leftBoundaryUpperIndex p q m hm t (Fin.last (p + 2))).suffixInput
            ((leftBoundaryUpperFace p q m t (Fin.last (p + 2))).succAbove x)
              (by rw [gap_leftBoundaryUpperIndex]; omega) =
          (Shuffle.leftBoundaryIndex t (Fin.last (p + 2))).succAbove
            (Fin.cast (by omega) z) := by
      apply Fin.ext
      simp only [suffixInput, hleftVal, z, Shuffle.leftBoundaryIndex_last,
        Fin.succAbove_last, Fin.val_castSucc, Fin.val_cast]
      rw [gap_leftBoundaryUpperIndex]
    have hsuffixRight :
        (rightBoundaryUpperIndex p q m hm t 0).suffixInput
            ((rightBoundaryUpperFace p q m t 0).succAbove x)
              (by rw [gap_rightBoundaryUpperIndex]; omega) =
          (Shuffle.rightBoundaryIndex t 0).succAbove (Fin.cast (by omega) z) := by
      apply Fin.ext
      simp only [suffixInput, hrightVal, z, Shuffle.rightBoundaryIndex_zero,
        Fin.zero_succAbove, Fin.val_succ, Fin.val_cast]
      rw [gap_rightBoundaryUpperIndex]
      rw [Nat.add_comm x.val 1, Nat.add_sub_assoc hxm,
        Nat.add_comm 1 (x.val - m)]
    change m - 1 +
        ((Shuffle.leftBoundaryShuffle t (Fin.last (p + 2))).leftHom.toOrderHom
          ((leftBoundaryUpperIndex p q m hm t (Fin.last (p + 2))).suffixInput
            ((leftBoundaryUpperFace p q m t (Fin.last (p + 2))).succAbove x)
              (by rw [gap_leftBoundaryUpperIndex]; omega))).val =
      m - 1 +
        ((Shuffle.rightBoundaryShuffle t 0).leftHom.toOrderHom
          ((rightBoundaryUpperIndex p q m hm t 0).suffixInput
            ((rightBoundaryUpperFace p q m t 0).succAbove x)
              (by rw [gap_rightBoundaryUpperIndex]; omega))).val
    rw [hsuffixLeft, hsuffixRight]
    have hleftShuffle := Shuffle.leftHom_leftBoundaryShuffle_succAbove
      t (Fin.last (p + 2)) z
    have hrightShuffle := Shuffle.leftHom_rightBoundaryShuffle_succAbove
      t (0 : Fin (q + 2)) z
    have hleftShuffleVal := congrArg Fin.val hleftShuffle
    have hrightShuffleVal := congrArg Fin.val hrightShuffle
    rw [hleftShuffleVal, hrightShuffleVal]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- Right-factor version of `delta_leftLast_comp_leftHom_eq_rightZero`. -/
theorem delta_leftLast_comp_rightHom_eq_rightZero
    (p q m : ℕ) (hm : 0 < m) (t : Shuffle (p + 1) q) :
    SimplexCategory.δ
          (leftBoundaryUpperFace p q m t (Fin.last (p + 2))) ≫
        (leftBoundaryUpperIndex p q m hm t (Fin.last (p + 2))).rightHom =
      SimplexCategory.δ (rightBoundaryUpperFace p q m t 0) ≫
        (rightBoundaryUpperIndex p q m hm t 0).rightHom := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext x
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, rightHom, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
    gap_leftBoundaryUpperIndex, gap_rightBoundaryUpperIndex]
  change
    (if _h :
        ((leftBoundaryUpperFace p q m t (Fin.last (p + 2))).succAbove x).val < m
      then _ else _) =
      (if _h : ((rightBoundaryUpperFace p q m t 0).succAbove x).val < m
        then _ else _)
  by_cases hx : x.val < m
  · have hleftFace :
        x.castSucc < leftBoundaryUpperFace p q m t (Fin.last (p + 2)) := by
      rw [leftBoundaryUpperFace_last]
      exact Fin.castSucc_lt_last x
    have hrightFace : x.castSucc < rightBoundaryUpperFace p q m t 0 := by
      rw [rightBoundaryUpperFace_zero]
      simpa [Fin.lt_def, transitionUpperFace] using hx
    have hleft :
        ((leftBoundaryUpperFace p q m t (Fin.last (p + 2))).succAbove x).val < m := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hleftFace]
      simpa only [Fin.val_castSucc] using hx
    have hright :
        ((rightBoundaryUpperFace p q m t 0).succAbove x).val < m := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hrightFace]
      simpa only [Fin.val_castSucc] using hx
    rw [dite_eq_left hleft, dite_eq_left hright]
    apply Fin.ext
    change
      ((leftBoundaryUpperFace p q m t (Fin.last (p + 2))).succAbove x).val =
        ((rightBoundaryUpperFace p q m t 0).succAbove x).val
    rw [Fin.succAbove_of_castSucc_lt _ _ hleftFace,
      Fin.succAbove_of_castSucc_lt _ _ hrightFace]
  · have hxm : m ≤ x.val := le_of_not_gt hx
    have hleftFace :
        x.castSucc < leftBoundaryUpperFace p q m t (Fin.last (p + 2)) := by
      rw [leftBoundaryUpperFace_last]
      exact Fin.castSucc_lt_last x
    have hrightFace : rightBoundaryUpperFace p q m t 0 ≤ x.castSucc := by
      rw [rightBoundaryUpperFace_zero]
      simpa [Fin.le_def, transitionUpperFace] using hxm
    have hleftVal :
        ((leftBoundaryUpperFace p q m t (Fin.last (p + 2))).succAbove x).val =
          x.val := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hleftFace]
      rfl
    have hrightVal :
        ((rightBoundaryUpperFace p q m t 0).succAbove x).val = x.val + 1 := by
      rw [Fin.succAbove_of_le_castSucc _ _ hrightFace]
      rfl
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]
    apply Fin.ext
    let z : Fin (p + 1 + q + 1) :=
      ⟨x.val - m, by
        have hxlt := x.isLt
        omega⟩
    have hsuffixLeft :
        (leftBoundaryUpperIndex p q m hm t (Fin.last (p + 2))).suffixInput
            ((leftBoundaryUpperFace p q m t (Fin.last (p + 2))).succAbove x)
              (by rw [gap_leftBoundaryUpperIndex]; omega) =
          (Shuffle.leftBoundaryIndex t (Fin.last (p + 2))).succAbove
            (Fin.cast (by omega) z) := by
      apply Fin.ext
      simp only [suffixInput, hleftVal, z, Shuffle.leftBoundaryIndex_last,
        Fin.succAbove_last, Fin.val_castSucc, Fin.val_cast]
      rw [gap_leftBoundaryUpperIndex]
    have hsuffixRight :
        (rightBoundaryUpperIndex p q m hm t 0).suffixInput
            ((rightBoundaryUpperFace p q m t 0).succAbove x)
              (by rw [gap_rightBoundaryUpperIndex]; omega) =
          (Shuffle.rightBoundaryIndex t 0).succAbove (Fin.cast (by omega) z) := by
      apply Fin.ext
      simp only [suffixInput, hrightVal, z, Shuffle.rightBoundaryIndex_zero,
        Fin.zero_succAbove, Fin.val_succ, Fin.val_cast]
      rw [gap_rightBoundaryUpperIndex]
      rw [Nat.add_comm x.val 1, Nat.add_sub_assoc hxm,
        Nat.add_comm 1 (x.val - m)]
    change m + (p + 1) +
        ((Shuffle.leftBoundaryShuffle t (Fin.last (p + 2))).rightHom.toOrderHom
          ((leftBoundaryUpperIndex p q m hm t (Fin.last (p + 2))).suffixInput
            ((leftBoundaryUpperFace p q m t (Fin.last (p + 2))).succAbove x)
              (by rw [gap_leftBoundaryUpperIndex]; omega))).val =
      m + p +
        ((Shuffle.rightBoundaryShuffle t 0).rightHom.toOrderHom
          ((rightBoundaryUpperIndex p q m hm t 0).suffixInput
            ((rightBoundaryUpperFace p q m t 0).succAbove x)
              (by rw [gap_rightBoundaryUpperIndex]; omega))).val
    rw [hsuffixLeft, hsuffixRight]
    have hleftShuffle := Shuffle.rightHom_leftBoundaryShuffle_succAbove
      t (Fin.last (p + 2)) z
    have hrightShuffle := Shuffle.rightHom_rightBoundaryShuffle_succAbove
      t (0 : Fin (q + 2)) z
    have hleftShuffleVal := congrArg Fin.val hleftShuffle
    have hrightShuffleVal := congrArg Fin.val hrightShuffle
    rw [hleftShuffleVal, hrightShuffleVal]
    simp only [Fin.zero_succAbove, Fin.val_succ]
    omega

end ShihIndex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- The transition face cancels the active face created by a zero left
insertion. -/
theorem shihTransitionBoundaryTerm_add_leftZero_eq_zero
    (X Y : SimplicialObject C) (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) :
    shihUpperBoundaryTerm X Y (p + q + m + 1)
          (ShihIndex.ofGap p q (m + 1) (by omega) t)
          (ShihIndex.transitionUpperFace p q m) +
        shihUpperBoundaryTerm X Y (p + q + m + 1)
          (ShihIndex.leftBoundaryUpperIndex p q m hm t 0)
          (ShihIndex.leftBoundaryUpperFace p q m t 0) = 0 := by
  unfold shihUpperBoundaryTerm shihSummand
  simp only [Preadditive.zsmul_comp,
    MonoidalCategory.tensorHom_comp_tensorHom]
  have hleft :
      X.map (ShihIndex.ofGap p q (m + 1) (by omega) t).leftHom.op ≫
          X.δ (ShihIndex.transitionUpperFace p q m) =
        X.map (ShihIndex.leftBoundaryUpperIndex p q m hm t 0).leftHom.op ≫
          X.δ (ShihIndex.leftBoundaryUpperFace p q m t 0) := by
    simpa [SimplicialObject.δ] using congrArg (fun f => X.map f.op)
      (ShihIndex.delta_transition_comp_leftHom_eq_leftZero p q m hm t)
  have hright :
      Y.map (ShihIndex.ofGap p q (m + 1) (by omega) t).rightHom.op ≫
          Y.δ (ShihIndex.transitionUpperFace p q m) =
        Y.map (ShihIndex.leftBoundaryUpperIndex p q m hm t 0).rightHom.op ≫
          Y.δ (ShihIndex.leftBoundaryUpperFace p q m t 0) := by
    simpa [SimplicialObject.δ] using congrArg (fun f => Y.map f.op)
      (ShihIndex.delta_transition_comp_rightHom_eq_leftZero p q m hm t)
  rw [hleft, hright, smul_smul, smul_smul, ← add_smul]
  have hc := ShihIndex.transitionCoefficient_add_leftZero_eq_zero p q m hm t
  unfold ShihIndex.leftUpperCoefficient at hc
  rw [hc]
  exact zero_smul _ _

/-- The final left insertion cancels the zero right insertion. -/
theorem shihLeftLastBoundaryTerm_add_rightZero_eq_zero
    (X Y : SimplicialObject C) (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) :
    shihUpperBoundaryTerm X Y (p + q + m + 1)
          (ShihIndex.leftBoundaryUpperIndex p q m hm t (Fin.last (p + 2)))
          (ShihIndex.leftBoundaryUpperFace p q m t (Fin.last (p + 2))) +
        shihUpperBoundaryTerm X Y (p + q + m + 1)
          (ShihIndex.rightBoundaryUpperIndex p q m hm t 0)
          (ShihIndex.rightBoundaryUpperFace p q m t 0) = 0 := by
  unfold shihUpperBoundaryTerm shihSummand
  simp only [Preadditive.zsmul_comp,
    MonoidalCategory.tensorHom_comp_tensorHom]
  have hleft :
      X.map (ShihIndex.leftBoundaryUpperIndex p q m hm t
            (Fin.last (p + 2))).leftHom.op ≫
          X.δ (ShihIndex.leftBoundaryUpperFace p q m t (Fin.last (p + 2))) =
        X.map (ShihIndex.rightBoundaryUpperIndex p q m hm t 0).leftHom.op ≫
          X.δ (ShihIndex.rightBoundaryUpperFace p q m t 0) := by
    simpa [SimplicialObject.δ] using congrArg (fun f => X.map f.op)
      (ShihIndex.delta_leftLast_comp_leftHom_eq_rightZero p q m hm t)
  have hright :
      Y.map (ShihIndex.leftBoundaryUpperIndex p q m hm t
            (Fin.last (p + 2))).rightHom.op ≫
          Y.δ (ShihIndex.leftBoundaryUpperFace p q m t (Fin.last (p + 2))) =
        Y.map (ShihIndex.rightBoundaryUpperIndex p q m hm t 0).rightHom.op ≫
          Y.δ (ShihIndex.rightBoundaryUpperFace p q m t 0) := by
    simpa [SimplicialObject.δ] using congrArg (fun f => Y.map f.op)
      (ShihIndex.delta_leftLast_comp_rightHom_eq_rightZero p q m hm t)
  rw [hleft, hright, smul_smul, smul_smul, ← add_smul]
  have hc := ShihIndex.leftLastCoefficient_add_rightZero_eq_zero p q m hm t
  unfold ShihIndex.leftUpperCoefficient ShihIndex.rightUpperCoefficient at hc
  rw [hc]
  exact zero_smul _ _

end AlgebraicTopology.EilenbergZilber
