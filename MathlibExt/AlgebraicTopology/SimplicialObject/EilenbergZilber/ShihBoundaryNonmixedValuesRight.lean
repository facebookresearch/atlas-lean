/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryNonmixedCancellation

/-!
# Values of inserted-right Shih boundary words

These lemmas isolate the dependent total-degree transports needed to compare
an inserted-right active face with its lower-boundary partner.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Simplicial

namespace AlgebraicTopology.EilenbergZilber.ShihIndex

/-- The active suffix coordinate of an inserted-right index is the local
boundary successor of the original active coordinate. -/
theorem rightBoundaryUpper_suffixInput_val (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2))
    (x : Fin (p + q + m + 2)) (hx : m ≤ x.val) :
    ((rightBoundaryUpperIndex p q m hm t b).suffixInput
        ((rightBoundaryUpperFace p q m t b).succAbove x) (by
          rw [gap_rightBoundaryUpperIndex]
          by_cases hface : x.castSucc < rightBoundaryUpperFace p q m t b
          · rw [Fin.succAbove_of_castSucc_lt _ _ hface]
            simpa using hx
          · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hface)]
            simp
            omega)).val =
      ((rightBoundaryLocalFace p q m hm t b).succAbove
        ((rightBoundaryUpperIndex p q m hm t b).activeInput x (by
          simpa only [gap_rightBoundaryUpperIndex] using hx))).val := by
  have hs := suffixInput_activeBoundaryFace_succAbove
    (rightBoundaryUpperIndex p q m hm t b)
    (rightBoundaryLocalFace p q m hm t b) x
    (by simpa only [gap_rightBoundaryUpperIndex] using hx)
  have hv := congrArg Fin.val hs
  simpa only [activeBoundaryFace_rightBoundaryLocalFace] using hv

set_option backward.isDefEq.respectTransparency false in
/-- The left shuffle coordinate after an inserted-right active face. -/
theorem rightBoundaryUpper_leftValue (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2))
    (x : Fin (p + q + m + 2)) (hx : m ≤ x.val) :
    (((rightBoundaryUpperIndex p q m hm t b).shuffle.leftHom.toOrderHom
      ((rightBoundaryUpperIndex p q m hm t b).suffixInput
        ((rightBoundaryUpperFace p q m t b).succAbove x) (by
          rw [gap_rightBoundaryUpperIndex]
          by_cases hface : x.castSucc < rightBoundaryUpperFace p q m t b
          · rw [Fin.succAbove_of_castSucc_lt _ _ hface]
            simpa using hx
          · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hface)]
            simp
            omega))).val) =
      ((ofGap p q m hm t).shuffle.leftHom.toOrderHom
        ((ofGap p q m hm t).suffixInput x (by
          rw [gap_ofGap]
          exact hx))).val := by
  let baseInput : Fin (p + 1 + q + 1) :=
    Fin.cast (by simp [ofGap])
      ((ofGap p q m hm t).suffixInput x (by simpa only [gap_ofGap] using hx))
  let upperInput : Fin (p + 1 + (q + 1) + 1) :=
    Fin.cast (by simp [rightBoundaryUpperIndex])
      ((rightBoundaryUpperIndex p q m hm t b).suffixInput
        ((rightBoundaryUpperFace p q m t b).succAbove x) (by
          rw [gap_rightBoundaryUpperIndex]
          by_cases hface : x.castSucc < rightBoundaryUpperFace p q m t b
          · rw [Fin.succAbove_of_castSucc_lt _ _ hface]
            simpa using hx
          · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hface)]
            simp
            omega))
  have hsuffixVal := rightBoundaryUpper_suffixInput_val p q m hm t b x hx
  have hactiveVal :
      ((rightBoundaryUpperIndex p q m hm t b).activeInput x (by
        simpa only [gap_rightBoundaryUpperIndex] using hx)).val = baseInput.val := by
    simp [activeInput, baseInput, suffixInput, gap_ofGap]
  have hinput : upperInput =
      (Shuffle.rightBoundaryIndex t b).succAbove (Fin.cast (by omega) baseInput) := by
    apply Fin.ext
    calc
      upperInput.val =
          ((rightBoundaryUpperIndex p q m hm t b).suffixInput
            ((rightBoundaryUpperFace p q m t b).succAbove x) (by
              rw [gap_rightBoundaryUpperIndex]
              by_cases hface : x.castSucc < rightBoundaryUpperFace p q m t b
              · rw [Fin.succAbove_of_castSucc_lt _ _ hface]
                simpa using hx
              · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hface)]
                simp
                omega)).val := by rfl
      _ = ((rightBoundaryLocalFace p q m hm t b).succAbove
          ((rightBoundaryUpperIndex p q m hm t b).activeInput x (by
            simpa only [gap_rightBoundaryUpperIndex] using hx))).val := hsuffixVal
      _ = ((Shuffle.rightBoundaryIndex t b).succAbove
          (Fin.cast (by omega) baseInput)).val := by
        apply congrArg Fin.val
        congr 1
        apply Fin.ext
        exact hactiveVal
  have hshuffle := Shuffle.leftHom_rightBoundaryShuffle_succAbove t b baseInput
  change ((Shuffle.rightBoundaryShuffle t b).leftHom.toOrderHom upperInput).val =
    (t.leftHom.toOrderHom baseInput).val
  rw [hinput]
  exact congrArg Fin.val hshuffle

set_option backward.isDefEq.respectTransparency false in
/-- The right shuffle coordinate after an inserted-right active face. -/
theorem rightBoundaryUpper_rightValue (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2))
    (x : Fin (p + q + m + 2)) (hx : m ≤ x.val) :
    (((rightBoundaryUpperIndex p q m hm t b).shuffle.rightHom.toOrderHom
      ((rightBoundaryUpperIndex p q m hm t b).suffixInput
        ((rightBoundaryUpperFace p q m t b).succAbove x) (by
          rw [gap_rightBoundaryUpperIndex]
          by_cases hface : x.castSucc < rightBoundaryUpperFace p q m t b
          · rw [Fin.succAbove_of_castSucc_lt _ _ hface]
            simpa using hx
          · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hface)]
            simp
            omega))).val) =
      (b.succAbove
        ((ofGap p q m hm t).shuffle.rightHom.toOrderHom
          ((ofGap p q m hm t).suffixInput x (by
            rw [gap_ofGap]
            exact hx)))).val := by
  let baseInput : Fin (p + 1 + q + 1) :=
    Fin.cast (by simp [ofGap])
      ((ofGap p q m hm t).suffixInput x (by simpa only [gap_ofGap] using hx))
  let upperInput : Fin (p + 1 + (q + 1) + 1) :=
    Fin.cast (by simp [rightBoundaryUpperIndex])
      ((rightBoundaryUpperIndex p q m hm t b).suffixInput
        ((rightBoundaryUpperFace p q m t b).succAbove x) (by
          rw [gap_rightBoundaryUpperIndex]
          by_cases hface : x.castSucc < rightBoundaryUpperFace p q m t b
          · rw [Fin.succAbove_of_castSucc_lt _ _ hface]
            simpa using hx
          · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hface)]
            simp
            omega))
  have hsuffixVal := rightBoundaryUpper_suffixInput_val p q m hm t b x hx
  have hactiveVal :
      ((rightBoundaryUpperIndex p q m hm t b).activeInput x (by
        simpa only [gap_rightBoundaryUpperIndex] using hx)).val = baseInput.val := by
    simp [activeInput, baseInput, suffixInput, gap_ofGap]
  have hinput : upperInput =
      (Shuffle.rightBoundaryIndex t b).succAbove (Fin.cast (by omega) baseInput) := by
    apply Fin.ext
    calc
      upperInput.val =
          ((rightBoundaryUpperIndex p q m hm t b).suffixInput
            ((rightBoundaryUpperFace p q m t b).succAbove x) (by
              rw [gap_rightBoundaryUpperIndex]
              by_cases hface : x.castSucc < rightBoundaryUpperFace p q m t b
              · rw [Fin.succAbove_of_castSucc_lt _ _ hface]
                simpa using hx
              · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hface)]
                simp
                omega)).val := by rfl
      _ = ((rightBoundaryLocalFace p q m hm t b).succAbove
          ((rightBoundaryUpperIndex p q m hm t b).activeInput x (by
            simpa only [gap_rightBoundaryUpperIndex] using hx))).val := hsuffixVal
      _ = ((Shuffle.rightBoundaryIndex t b).succAbove
          (Fin.cast (by omega) baseInput)).val := by
        apply congrArg Fin.val
        congr 1
        apply Fin.ext
        exact hactiveVal
  have hshuffle := Shuffle.rightHom_rightBoundaryShuffle_succAbove t b baseInput
  change ((Shuffle.rightBoundaryShuffle t b).rightHom.toOrderHom upperInput).val =
    (b.succAbove (t.rightHom.toOrderHom baseInput)).val
  rw [hinput]
  exact congrArg Fin.val hshuffle

end AlgebraicTopology.EilenbergZilber.ShihIndex
