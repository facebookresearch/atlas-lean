/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryNonmixedCancellation

/-!
# Values of inserted-left Shih boundary words

These lemmas isolate the dependent total-degree transports needed to compare
an inserted-left active face with its lower-boundary partner.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Simplicial

namespace AlgebraicTopology.EilenbergZilber.ShihIndex

/-- The active suffix coordinate of an inserted-left index is the local
boundary successor of the original active coordinate. -/
theorem leftBoundaryUpper_suffixInput_val (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3))
    (x : Fin (p + q + m + 2)) (hx : m ≤ x.val) :
    ((leftBoundaryUpperIndex p q m hm t a).suffixInput
        ((leftBoundaryUpperFace p q m t a).succAbove x) (by
          rw [gap_leftBoundaryUpperIndex]
          by_cases hface : x.castSucc < leftBoundaryUpperFace p q m t a
          · rw [Fin.succAbove_of_castSucc_lt _ _ hface]
            simpa using hx
          · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hface)]
            simp
            omega)).val =
      ((leftBoundaryLocalFace p q m hm t a).succAbove
        ((leftBoundaryUpperIndex p q m hm t a).activeInput x (by
          simpa only [gap_leftBoundaryUpperIndex] using hx))).val := by
  have hs := suffixInput_activeBoundaryFace_succAbove
    (leftBoundaryUpperIndex p q m hm t a)
    (leftBoundaryLocalFace p q m hm t a) x
    (by simpa only [gap_leftBoundaryUpperIndex] using hx)
  have hv := congrArg Fin.val hs
  simpa only [activeBoundaryFace_leftBoundaryLocalFace] using hv

set_option backward.isDefEq.respectTransparency false in
/-- The left shuffle coordinate after an inserted-left active face. -/
theorem leftBoundaryUpper_leftValue (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3))
    (x : Fin (p + q + m + 2)) (hx : m ≤ x.val) :
    (((leftBoundaryUpperIndex p q m hm t a).shuffle.leftHom.toOrderHom
      ((leftBoundaryUpperIndex p q m hm t a).suffixInput
        ((leftBoundaryUpperFace p q m t a).succAbove x) (by
          rw [gap_leftBoundaryUpperIndex]
          by_cases hface : x.castSucc < leftBoundaryUpperFace p q m t a
          · rw [Fin.succAbove_of_castSucc_lt _ _ hface]
            simpa using hx
          · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hface)]
            simp
            omega))).val) =
      (a.succAbove
        ((ofGap p q m hm t).shuffle.leftHom.toOrderHom
          ((ofGap p q m hm t).suffixInput x (by
            rw [gap_ofGap]
            exact hx)))).val := by
  let baseInput : Fin (p + 1 + q + 1) :=
    Fin.cast (by simp [ofGap])
      ((ofGap p q m hm t).suffixInput x (by simpa only [gap_ofGap] using hx))
  let upperInput : Fin ((p + 1) + 1 + q + 1) :=
    Fin.cast (by simp [leftBoundaryUpperIndex])
      ((leftBoundaryUpperIndex p q m hm t a).suffixInput
        ((leftBoundaryUpperFace p q m t a).succAbove x) (by
          rw [gap_leftBoundaryUpperIndex]
          by_cases hface : x.castSucc < leftBoundaryUpperFace p q m t a
          · rw [Fin.succAbove_of_castSucc_lt _ _ hface]
            simpa using hx
          · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hface)]
            simp
            omega))
  have hsuffixVal := leftBoundaryUpper_suffixInput_val p q m hm t a x hx
  have hactiveVal :
      ((leftBoundaryUpperIndex p q m hm t a).activeInput x (by
        simpa only [gap_leftBoundaryUpperIndex] using hx)).val = baseInput.val := by
    simp [activeInput, baseInput, suffixInput, gap_ofGap]
  have hinput : upperInput =
      (Shuffle.leftBoundaryIndex t a).succAbove (Fin.cast (by omega) baseInput) := by
    apply Fin.ext
    calc
      upperInput.val =
          ((leftBoundaryUpperIndex p q m hm t a).suffixInput
            ((leftBoundaryUpperFace p q m t a).succAbove x) (by
              rw [gap_leftBoundaryUpperIndex]
              by_cases hface : x.castSucc < leftBoundaryUpperFace p q m t a
              · rw [Fin.succAbove_of_castSucc_lt _ _ hface]
                simpa using hx
              · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hface)]
                simp
                omega)).val := by rfl
      _ = ((leftBoundaryLocalFace p q m hm t a).succAbove
          ((leftBoundaryUpperIndex p q m hm t a).activeInput x (by
            simpa only [gap_leftBoundaryUpperIndex] using hx))).val := hsuffixVal
      _ = ((Shuffle.leftBoundaryIndex t a).succAbove
          (Fin.cast (by omega) baseInput)).val := by
        apply congrArg Fin.val
        congr 1
        apply Fin.ext
        exact hactiveVal
  have hshuffle := Shuffle.leftHom_leftBoundaryShuffle_succAbove t a baseInput
  change ((Shuffle.leftBoundaryShuffle t a).leftHom.toOrderHom upperInput).val =
    (a.succAbove (t.leftHom.toOrderHom baseInput)).val
  rw [hinput]
  exact congrArg Fin.val hshuffle

set_option backward.isDefEq.respectTransparency false in
/-- The right shuffle coordinate after an inserted-left active face. -/
theorem leftBoundaryUpper_rightValue (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3))
    (x : Fin (p + q + m + 2)) (hx : m ≤ x.val) :
    (((leftBoundaryUpperIndex p q m hm t a).shuffle.rightHom.toOrderHom
      ((leftBoundaryUpperIndex p q m hm t a).suffixInput
        ((leftBoundaryUpperFace p q m t a).succAbove x) (by
          rw [gap_leftBoundaryUpperIndex]
          by_cases hface : x.castSucc < leftBoundaryUpperFace p q m t a
          · rw [Fin.succAbove_of_castSucc_lt _ _ hface]
            simpa using hx
          · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hface)]
            simp
            omega))).val) =
      ((ofGap p q m hm t).shuffle.rightHom.toOrderHom
        ((ofGap p q m hm t).suffixInput x (by
          rw [gap_ofGap]
          exact hx))).val := by
  let baseInput : Fin (p + 1 + q + 1) :=
    Fin.cast (by simp [ofGap])
      ((ofGap p q m hm t).suffixInput x (by simpa only [gap_ofGap] using hx))
  let upperInput : Fin ((p + 1) + 1 + q + 1) :=
    Fin.cast (by simp [leftBoundaryUpperIndex])
      ((leftBoundaryUpperIndex p q m hm t a).suffixInput
        ((leftBoundaryUpperFace p q m t a).succAbove x) (by
          rw [gap_leftBoundaryUpperIndex]
          by_cases hface : x.castSucc < leftBoundaryUpperFace p q m t a
          · rw [Fin.succAbove_of_castSucc_lt _ _ hface]
            simpa using hx
          · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hface)]
            simp
            omega))
  have hsuffixVal := leftBoundaryUpper_suffixInput_val p q m hm t a x hx
  have hactiveVal :
      ((leftBoundaryUpperIndex p q m hm t a).activeInput x (by
        simpa only [gap_leftBoundaryUpperIndex] using hx)).val = baseInput.val := by
    simp [activeInput, baseInput, suffixInput, gap_ofGap]
  have hinput : upperInput =
      (Shuffle.leftBoundaryIndex t a).succAbove (Fin.cast (by omega) baseInput) := by
    apply Fin.ext
    calc
      upperInput.val =
          ((leftBoundaryUpperIndex p q m hm t a).suffixInput
            ((leftBoundaryUpperFace p q m t a).succAbove x) (by
              rw [gap_leftBoundaryUpperIndex]
              by_cases hface : x.castSucc < leftBoundaryUpperFace p q m t a
              · rw [Fin.succAbove_of_castSucc_lt _ _ hface]
                simpa using hx
              · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hface)]
                simp
                omega)).val := by rfl
      _ = ((leftBoundaryLocalFace p q m hm t a).succAbove
          ((leftBoundaryUpperIndex p q m hm t a).activeInput x (by
            simpa only [gap_leftBoundaryUpperIndex] using hx))).val := hsuffixVal
      _ = ((Shuffle.leftBoundaryIndex t a).succAbove
          (Fin.cast (by omega) baseInput)).val := by
        apply congrArg Fin.val
        congr 1
        apply Fin.ext
        exact hactiveVal
  have hshuffle := Shuffle.rightHom_leftBoundaryShuffle_succAbove t a baseInput
  change ((Shuffle.leftBoundaryShuffle t a).rightHom.toOrderHom upperInput).val =
    (t.rightHom.toOrderHom baseInput).val
  rw [hinput]
  exact congrArg Fin.val hshuffle

end AlgebraicTopology.EilenbergZilber.ShihIndex
