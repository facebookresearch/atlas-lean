/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

-- Author: @toskua
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialGroupLowerHornCorrection

/-! # Actual upper-face corrections preserving the SAME lower and later group faces -/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.SimplicialGroupHorn

attribute [local instance] underlyingGroup

variable (G : SimplicialObject GrpCat.{u})

/-- The actual upper-face error preserves the original noncommutative coefficient order. -/
def upperError {n : ℕ} (j : Fin (n + 1)) (x : (underlying G) _⦋n + 1⦌)
    (h : (underlying G) _⦋n⦌) : (underlying G) _⦋n⦌ := ((underlying G).δ j.succ x)⁻¹ * h

/-- Correct the SAME original upper face by its matching degeneracy and original group error. -/
def correctUpper {n : ℕ} (j : Fin (n + 1)) (x : (underlying G) _⦋n + 1⦌)
    (h : (underlying G) _⦋n⦌) : (underlying G) _⦋n + 1⦌ := x * (underlying G).σ j (upperError G j x h)

/-- The complete original matching upper face is exactly the prescribed face after correction. -/
theorem correctUpper_face {n : ℕ} (j : Fin (n + 1)) (x : (underlying G) _⦋n + 1⦌)
    (h : (underlying G) _⦋n⦌) : (underlying G).δ j.succ (correctUpper G j x h) = h := by
  have hm := operator_mul G (SimplexCategory.δ j.succ).op x ((underlying G).σ j (upperError G j x h))
  have hd := face_degeneracy_succ G j (upperError G j x h)
  exact hm.trans ((congrArg (fun y => (underlying G).δ j.succ x * y) hd).trans (mul_inv_cancel_left _ h))

/-- Every previously fixed lower face has trivial actual upper correction error by original face compatibility. -/
theorem upperError_lower_face_one {n : ℕ} {k j : Fin (n + 2)} (hkj : k < j)
    (x : (underlying G) _⦋n + 2⦌) (a b : (underlying G) _⦋n + 1⦌)
    (hx : (underlying G).δ (Fin.castSucc k) x = b)
    (hc : (underlying G).δ k a = (underlying G).δ j b) :
    (underlying G).δ k (upperError G j x a) = 1 := by
  have hlt : Fin.castSucc k < j.succ := lt_trans (Fin.castSucc_lt_castSucc_iff.mpr hkj)
    (show Fin.castSucc j < j.succ from Nat.lt_succ_self j.val)
  have hh := ConcreteCategory.congr_hom ((underlying G).δ_comp_δ' hlt) x
  have hd : (underlying G).δ k ((underlying G).δ j.succ x) = (underlying G).δ j b := by
    have h := (congrArg ((underlying G).δ j) hx)
    simpa only [Fin.pred_succ, CategoryTheory.types_comp_apply] using hh.trans h
  have hm := operator_mul G (SimplexCategory.δ k).op (((underlying G).δ j.succ x)⁻¹) a
  have hi := operator_inv G (SimplexCategory.δ k).op ((underlying G).δ j.succ x)
  exact hm.trans ((congrArg₂ (fun y z => y * z) (hi.trans (congrArg Inv.inv hd)) hc).trans (inv_mul_cancel _))

/-- The actual upper correction preserves every already fixed lower face strictly before its degeneracy. -/
theorem correctUpper_preserves_lower {n : ℕ} {k j : Fin (n + 2)} (hkj : k < j)
    (x : (underlying G) _⦋n + 2⦌) (a b : (underlying G) _⦋n + 1⦌)
    (hx : (underlying G).δ (Fin.castSucc k) x = b)
    (hc : (underlying G).δ k a = (underlying G).δ j b) :
    (underlying G).δ (Fin.castSucc k) (correctUpper G j x a) = b := by
  let p := j.pred hkj.ne_zero
  have hp : k ≤ Fin.castSucc p := (Fin.le_castSucc_pred_iff hkj.ne_zero).mpr hkj
  have hs := ConcreteCategory.congr_hom ((underlying G).δ_comp_σ_of_le hp) (upperError G j x a)
  have he : (underlying G).δ (Fin.castSucc k) ((underlying G).σ j (upperError G j x a)) =
      (underlying G).σ p ((underlying G).δ k (upperError G j x a)) := by
    simpa only [p, Fin.succ_pred, CategoryTheory.types_comp_apply] using hs
  have hz := he.trans ((congrArg ((underlying G).σ p) (upperError_lower_face_one G hkj x a b hx hc)).trans
    (operator_one G (SimplexCategory.σ p).op))
  have hm := operator_mul G (SimplexCategory.δ (Fin.castSucc k)).op x ((underlying G).σ j (upperError G j x a))
  exact hm.trans ((congrArg₂ (fun y z => y * z) hx hz).trans (mul_one b))

/-- The actual upper-tail degeneracy retains the original finite scalar index. -/
def upperTailDeg {n : ℕ} {j : Fin (n + 2)} {k : Fin (n + 3)} (hjk : j.succ < k) : Fin (n + 1) :=
  j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le hjk k.is_le))

/-- The original compatible later face makes the SAME upper correction error trivial at its preceding face. -/
theorem upperError_later_face_one {n : ℕ} {j : Fin (n + 2)} {k : Fin (n + 3)} (hjk : j.succ < k)
    (x : (underlying G) _⦋n + 2⦌) (a b : (underlying G) _⦋n + 1⦌)
    (hx : (underlying G).δ k x = b)
    (hc : (underlying G).δ (upperTailDeg hjk).succ b = (underlying G).δ (k.pred hjk.ne_zero) a) :
    (underlying G).δ (k.pred hjk.ne_zero) (upperError G j x a) = 1 := by
  have hp : Fin.castSucc (upperTailDeg hjk).succ = j.succ := Fin.ext rfl
  have hlt : Fin.castSucc (upperTailDeg hjk).succ < k := by rw [hp]; exact hjk
  have hh := ConcreteCategory.congr_hom ((underlying G).δ_comp_δ' hlt) x
  have hd : (underlying G).δ (k.pred hjk.ne_zero) ((underlying G).δ j.succ x) =
      (underlying G).δ (upperTailDeg hjk).succ b := by
    have h := (congrArg ((underlying G).δ (upperTailDeg hjk).succ) hx)
    simpa only [hp, CategoryTheory.types_comp_apply] using hh.symm.trans h
  have hm := operator_mul G (SimplexCategory.δ (k.pred hjk.ne_zero)).op (((underlying G).δ j.succ x)⁻¹) a
  have hi := operator_inv G (SimplexCategory.δ (k.pred hjk.ne_zero)).op ((underlying G).δ j.succ x)
  exact hm.trans ((congrArg₂ (fun y z => y * z) (hi.trans (congrArg Inv.inv hd)) hc.symm).trans (inv_mul_cancel _))

/-- The actual upper correction preserves EVERY already fixed later original face. -/
theorem correctUpper_preserves_later {n : ℕ} {j : Fin (n + 2)} {k : Fin (n + 3)} (hjk : j.succ < k)
    (x : (underlying G) _⦋n + 2⦌) (a b : (underlying G) _⦋n + 1⦌)
    (hx : (underlying G).δ k x = b)
    (hc : (underlying G).δ (upperTailDeg hjk).succ b = (underlying G).δ (k.pred hjk.ne_zero) a) :
    (underlying G).δ k (correctUpper G j x a) = b := by
  have hs := ConcreteCategory.congr_hom ((underlying G).δ_comp_σ_of_gt' hjk) (upperError G j x a)
  have hz : (underlying G).δ k ((underlying G).σ j (upperError G j x a)) = 1 :=
    hs.trans ((congrArg ((underlying G).σ (upperTailDeg hjk)) (upperError_later_face_one G hjk x a b hx hc)).trans
      (operator_one G (SimplexCategory.σ (upperTailDeg hjk)).op))
  have hm := operator_mul G (SimplexCategory.δ k).op x ((underlying G).σ j (upperError G j x a))
  exact hm.trans ((congrArg₂ (fun y z => y * z) hx hz).trans (mul_one b))

/-- The actual finite upper pass starts at the SAME original lower filler and retains all prescribed coefficients. -/
def upperPass {n : ℕ} (i : Fin (n + 3)) (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌) (r : Fin (n + 3)) :
    (underlying G) _⦋n + 2⦌ :=
  Fin.reverseInduction (lowerPass G h i) (fun j x => correctUpper G j x (h j.succ)) r

/-- The original last upper stage is exactly the proved original lower pass. -/
theorem upperPass_last {n : ℕ} (i : Fin (n + 3)) (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌) :
    upperPass G i h (Fin.last (n + 2)) = lowerPass G h i := by
  simp only [upperPass, Fin.reverseInduction_last]

/-- Every actual descending stage corrects the SAME original next face through the actual group degeneracy. -/
theorem upperPass_castSucc {n : ℕ} (i : Fin (n + 3)) (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌)
    (j : Fin (n + 2)) : upperPass G i h (Fin.castSucc j) =
      correctUpper G j (upperPass G i h j.succ) (h j.succ) := by
  simp only [upperPass, Fin.reverseInduction_castSucc]

/-- The entire upper pass preserves ALL original lower faces and fills EVERY original later face. -/
theorem upperPass_faces {n : ℕ} (i : Fin (n + 3)) (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌)
    (hc : FaceCompatible G i h) (r : Fin (n + 3)) (hr : i ≤ r) :
    (∀ (k : Fin (n + 3)), k < i → (underlying G).δ k (upperPass G i h r) = h k) ∧
      (∀ (k : Fin (n + 3)), r < k → (underlying G).δ k (upperPass G i h r) = h k) := by
  induction r using Fin.reverseInduction with
  | last =>
    rw [upperPass_last]
    exact ⟨fun k hk => lowerPass_below G i h hc k hk,
      fun k hk => (not_lt_of_ge (Fin.le_last k) hk).elim⟩
  | cast j ih =>
    have hji : i < j.succ := lt_of_le_of_lt hr (show Fin.castSucc j < j.succ from Nat.lt_succ_self j.val)
    have hi := ih (le_of_lt hji)
    rw [upperPass_castSucc]
    constructor
    · intro k hki
      have hkj : k < Fin.castSucc j := lt_of_lt_of_le hki hr
      have hklast : k ≠ Fin.last (n + 2) := ne_of_lt (lt_trans hkj (Fin.castSucc_lt_last j))
      let k' := k.castPred hklast
      have hk' : Fin.castSucc k' = k := Fin.castSucc_castPred k hklast
      have hkj' : k' < j := Fin.castSucc_lt_castSucc_iff.mp (by rw [hk']; exact hkj)
      have hx : (underlying G).δ (Fin.castSucc k') (upperPass G i h j.succ) = h (Fin.castSucc k') := by
        simpa only [hk'] using hi.1 k hki
      have hlt : Fin.castSucc k' < j.succ := by
        rw [hk']
        exact lt_trans hkj (show Fin.castSucc j < j.succ from Nat.lt_succ_self j.val)
      have hp := hc k' j.succ hlt (by rw [hk']; exact ne_of_lt hki) (ne_of_gt hji)
      have hp' : (underlying G).δ k' (h j.succ) = (underlying G).δ j (h (Fin.castSucc k')) := by
        simpa only [Fin.pred_succ] using hp
      have hf := correctUpper_preserves_lower G hkj' (upperPass G i h j.succ)
        (h j.succ) (h (Fin.castSucc k')) hx hp'
      simpa only [hk'] using hf
    · intro k hjk
      by_cases he : k = j.succ
      · subst k
        exact correctUpper_face G j _ _
      · have hjk' : j.succ < k := by
          have hv : j.val < k.val := hjk
          have hn : j.val + 1 ≠ k.val := fun e => he (Fin.ext e.symm)
          exact Fin.lt_def.mpr (lt_of_le_of_ne (Nat.succ_le_iff.mpr hv) hn)
        have hx := hi.2 k hjk'
        have hp : Fin.castSucc (upperTailDeg hjk').succ = j.succ := Fin.ext rfl
        have hlt : Fin.castSucc (upperTailDeg hjk').succ < k := by rw [hp]; exact hjk'
        have hh := hc (upperTailDeg hjk').succ k hlt
          (by rw [hp]; exact ne_of_gt hji) (ne_of_gt (lt_trans hji hjk'))
        have hh' : (underlying G).δ (upperTailDeg hjk').succ (h k) =
            (underlying G).δ (k.pred hjk'.ne_zero) (h j.succ) := by
          simpa only [hp] using hh
        exact correctUpper_preserves_later G hjk' (upperPass G i h j.succ) (h j.succ) (h k) hx hh'

/-- The SAME actual finite passes give the complete original horn filler without a Kan premise. -/
def hornFiller {n : ℕ} (i : Fin (n + 3)) (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌) :
    (underlying G) _⦋n + 2⦌ := upperPass G i h i

/-- Every originally prescribed nonmissing face is retained by the WHOLE actual group horn filler. -/
theorem hornFiller_face {n : ℕ} (i : Fin (n + 3)) (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌)
    (hc : FaceCompatible G i h) (k : Fin (n + 3)) (hki : k ≠ i) :
    (underlying G).δ k (hornFiller G i h) = h k := by
  have hx := upperPass_faces G i h hc i (le_refl i)
  rcases lt_or_gt_of_ne hki with h | h
  · exact hx.1 k h
  · exact hx.2 k h

end SSet.SimplicialGroupHorn
