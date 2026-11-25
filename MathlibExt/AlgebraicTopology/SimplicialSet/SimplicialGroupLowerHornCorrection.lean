/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

-- Author: @toskua
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialGroupHornOperators
public import Mathlib.Data.Fin.SuccPred

/-! # Actual lower-face corrections in the SAME original simplicial group -/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.SimplicialGroupHorn

attribute [local instance] underlyingGroup

variable (G : SimplicialObject GrpCat.{u})

/-- The original prescribed-face error retains its actual noncommutative group multiplication order. -/
def lowerError {n : ℕ} (j : Fin (n + 1)) (x : (underlying G) _⦋n + 1⦌)
    (h : (underlying G) _⦋n⦌) : (underlying G) _⦋n⦌ :=
  ((underlying G).δ (Fin.castSucc j) x)⁻¹ * h

/-- Correct one original lower face using the genuine matching degeneracy and original group error. -/
def correctLower {n : ℕ} (j : Fin (n + 1)) (x : (underlying G) _⦋n + 1⦌)
    (h : (underlying G) _⦋n⦌) : (underlying G) _⦋n + 1⦌ :=
  x * (underlying G).σ j (lowerError G j x h)

/-- The whole original matching face of the actual corrected simplex is exactly the prescribed face. -/
theorem correctLower_face {n : ℕ} (j : Fin (n + 1)) (x : (underlying G) _⦋n + 1⦌)
    (h : (underlying G) _⦋n⦌) : (underlying G).δ (Fin.castSucc j) (correctLower G j x h) = h := by
  have hm := operator_mul G (SimplexCategory.δ (Fin.castSucc j)).op x
    ((underlying G).σ j (lowerError G j x h))
  have hd := face_degeneracy_self G j (lowerError G j x h)
  exact hm.trans ((congrArg (fun y => (underlying G).δ (Fin.castSucc j) x * y) hd).trans
    (mul_inv_cancel_left _ h))

/-- A face already correct has the SAME original group unit error. -/
theorem lowerError_one {n : ℕ} (j : Fin (n + 1)) (x : (underlying G) _⦋n + 1⦌)
    (h : (underlying G) _⦋n⦌) (hx : (underlying G).δ (Fin.castSucc j) x = h) :
    lowerError G j x h = 1 := by
  exact (congrArg (fun y => y⁻¹ * h) hx).trans (inv_mul_cancel h)

/-- The exact original preceding face index is retained in the lower-pair compatibility equation. -/
def lowerPairPred {n : ℕ} {k j : Fin (n + 2)} (hkj : k < j) : Fin (n + 2) :=
  (Fin.castSucc j).pred ((Fin.castSucc_lt_castSucc_iff.mpr hkj).ne_zero)

/-- Actual face compatibility and the previously fixed face make the SAME original group error trivial there. -/
theorem lowerError_face_one {n : ℕ} {k j : Fin (n + 2)} (hkj : k < j)
    (x : (underlying G) _⦋n + 2⦌) (a b : (underlying G) _⦋n + 1⦌)
    (hx : (underlying G).δ (Fin.castSucc k) x = b)
    (hc : (underlying G).δ k a = (underlying G).δ (lowerPairPred hkj) b) :
    (underlying G).δ k (lowerError G j x a) = 1 := by
  have hh := ConcreteCategory.congr_hom
    ((underlying G).δ_comp_δ' (Fin.castSucc_lt_castSucc_iff.mpr hkj)) x
  have hd : (underlying G).δ k ((underlying G).δ (Fin.castSucc j) x) =
      (underlying G).δ (lowerPairPred hkj) b :=
    hh.trans (congrArg ((underlying G).δ (lowerPairPred hkj)) hx)
  have hm := operator_mul G (SimplexCategory.δ k).op (((underlying G).δ (Fin.castSucc j) x)⁻¹) a
  have hi := operator_inv G (SimplexCategory.δ k).op ((underlying G).δ (Fin.castSucc j) x)
  exact hm.trans ((congrArg₂ (fun y z => y * z) (hi.trans (congrArg Inv.inv hd)) hc).trans
    (inv_mul_cancel _))

/-- The correction preserves every earlier actual prescribed face, with all original finite indices explicit. -/
theorem correctLower_preserves {n : ℕ} {k j : Fin (n + 2)} (hkj : k < j)
    (x : (underlying G) _⦋n + 2⦌) (a b : (underlying G) _⦋n + 1⦌)
    (hx : (underlying G).δ (Fin.castSucc k) x = b)
    (hc : (underlying G).δ k a = (underlying G).δ (lowerPairPred hkj) b) :
    (underlying G).δ (Fin.castSucc k) (correctLower G j x a) = b := by
  let p := j.pred hkj.ne_zero
  have hp : k ≤ Fin.castSucc p := (Fin.le_castSucc_pred_iff hkj.ne_zero).mpr hkj
  have hs := ConcreteCategory.congr_hom ((underlying G).δ_comp_σ_of_le hp) (lowerError G j x a)
  have he : (underlying G).δ (Fin.castSucc k) ((underlying G).σ j (lowerError G j x a)) =
      (underlying G).σ p ((underlying G).δ k (lowerError G j x a)) := by
    simpa only [p, Fin.succ_pred, CategoryTheory.types_comp_apply] using hs
  have hz : (underlying G).δ (Fin.castSucc k) ((underlying G).σ j (lowerError G j x a)) = 1 :=
    he.trans ((congrArg ((underlying G).σ p) (lowerError_face_one G hkj x a b hx hc)).trans
      (operator_one G (SimplexCategory.σ p).op))
  have hm := operator_mul G (SimplexCategory.δ (Fin.castSucc k)).op x
    ((underlying G).σ j (lowerError G j x a))
  exact hm.trans ((congrArg₂ (fun y z => y * z) hx hz).trans (mul_one b))

/-- The whole original group face family retains every actual horn compatibility equation off the missing face. -/
def FaceCompatible {n : ℕ} (i : Fin (n + 3)) (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌) : Prop :=
  ∀ (k : Fin (n + 2)) (j : Fin (n + 3)) (hkj : Fin.castSucc k < j)
    (_ : Fin.castSucc k ≠ i) (_ : j ≠ i),
      (underlying G).δ k (h j) = (underlying G).δ (j.pred hkj.ne_zero) (h (Fin.castSucc k))

/-- The actual finite lower pass starts at the original group unit and keeps every original correction coefficient. -/
def lowerPass {n : ℕ} (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌) (r : Fin (n + 3)) :
    (underlying G) _⦋n + 2⦌ :=
  Fin.induction 1 (fun j x => correctLower G j x (h (Fin.castSucc j))) r

/-- The actual zero-stage lower pass is the SAME original group unit. -/
theorem lowerPass_zero {n : ℕ} (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌) : lowerPass G h 0 = 1 := rfl

/-- Every finite successor stage uses exactly the actual matching correction and original prescribed face. -/
theorem lowerPass_succ {n : ℕ} (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌) (j : Fin (n + 2)) :
    lowerPass G h j.succ = correctLower G j (lowerPass G h (Fin.castSucc j)) (h (Fin.castSucc j)) := by
  simp only [lowerPass, Fin.induction_succ]

/-- The entire finite lower pass preserves and fills ALL original prescribed faces below its actual stage. -/
theorem lowerPass_faces {n : ℕ} (i : Fin (n + 3)) (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌)
    (hc : FaceCompatible G i h) (r : Fin (n + 3)) (hr : r ≤ i) (k : Fin (n + 3)) (hkr : k < r) :
    (underlying G).δ k (lowerPass G h r) = h k := by
  induction r using Fin.induction with
  | zero => exact (not_lt_of_ge (Fin.zero_le k) hkr).elim
  | succ j ih =>
    have hjlt : Fin.castSucc j < i := lt_of_lt_of_le (show Fin.castSucc j < j.succ from Nat.lt_succ_self j.val) hr
    have hjle : Fin.castSucc j ≤ i := le_of_lt hjlt
    rw [lowerPass_succ]
    by_cases he : k = Fin.castSucc j
    · subst k
      exact correctLower_face G j _ _
    · have hklt : k < Fin.castSucc j := by
        have hv : k.val < j.val + 1 := hkr
        have hn : k.val ≠ j.val := fun e => he (Fin.ext e)
        exact Fin.lt_def.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp hv) hn)
      have hklast : k ≠ Fin.last (n + 2) := ne_of_lt (lt_trans hklt (Fin.castSucc_lt_last j))
      let k' := k.castPred hklast
      have hk' : Fin.castSucc k' = k := Fin.castSucc_castPred k hklast
      have hkj : k' < j := Fin.castSucc_lt_castSucc_iff.mp (by rw [hk']; exact hklt)
      have hx : (underlying G).δ (Fin.castSucc k') (lowerPass G h (Fin.castSucc j)) = h (Fin.castSucc k') := by
        simpa only [hk'] using ih hjle hklt
      have hp := hc k' (Fin.castSucc j) (Fin.castSucc_lt_castSucc_iff.mpr hkj)
        (ne_of_lt (lt_trans (Fin.castSucc_lt_castSucc_iff.mpr hkj) hjlt)) (ne_of_lt hjlt)
      have hf := correctLower_preserves G hkj (lowerPass G h (Fin.castSucc j))
        (h (Fin.castSucc j)) (h (Fin.castSucc k')) hx hp
      simpa only [hk'] using hf

/-- The actual lower pass at the missing face fills every original face strictly below it. -/
theorem lowerPass_below {n : ℕ} (i : Fin (n + 3)) (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌)
    (hc : FaceCompatible G i h) (k : Fin (n + 3)) (hki : k < i) :
    (underlying G).δ k (lowerPass G h i) = h k := lowerPass_faces G i h hc i (le_refl i) k hki

end SSet.SimplicialGroupHorn
