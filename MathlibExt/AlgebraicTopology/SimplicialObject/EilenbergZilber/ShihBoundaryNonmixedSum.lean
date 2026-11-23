/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryNonmixedCancellation

/-!
# Additive assembly for nonmixed Shih boundary cancellations

This file turns simplex-word comparisons into pointwise and finite-sum
cancellation statements.  The combinatorial word proofs remain independent
of the preadditive target category.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- Once the two simplex-word comparisons are known, an interior inserted-left
upper face cancels its lower-boundary partner. -/
theorem shihLeftBoundaryTerm_add_lower_eq_zero_of_maps
    (X Y : SimplicialObject C) (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3))
    (ha0 : 0 < a.val) (_haLast : a.val < p + 2)
    (hleft :
      X.map (ShihIndex.leftBoundaryUpperIndex p q m hm t a).leftHom.op ≫
          X.δ (ShihIndex.leftBoundaryUpperFace p q m t a) =
        X.δ (ShihIndex.leftBoundaryLowerFace p q m hm a ha0) ≫
          X.map (ShihIndex.ofGap p q m hm t).leftHom.op)
    (hright :
      Y.map (ShihIndex.leftBoundaryUpperIndex p q m hm t a).rightHom.op ≫
          Y.δ (ShihIndex.leftBoundaryUpperFace p q m t a) =
        Y.δ (ShihIndex.leftBoundaryLowerFace p q m hm a ha0) ≫
          Y.map (ShihIndex.ofGap p q m hm t).rightHom.op) :
    shihUpperBoundaryTerm X Y (p + q + m + 1)
        (ShihIndex.leftBoundaryUpperIndex p q m hm t a)
        (ShihIndex.leftBoundaryUpperFace p q m t a) +
      shihLowerBoundaryTerm X Y (p + q + m)
        (ShihIndex.leftBoundaryLowerFace p q m hm a ha0)
        (ShihIndex.ofGap p q m hm t) = 0 := by
  unfold shihUpperBoundaryTerm shihLowerBoundaryTerm shihSummand
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    MonoidalCategory.tensorHom_comp_tensorHom]
  rw [hleft, hright]
  simp only [smul_smul]
  rw [← add_smul]
  change
    (ShihIndex.leftUpperCoefficient p q m hm t a +
      ShihIndex.leftLowerCoefficient p q m hm t a ha0) • _ = 0
  rw [ShihIndex.leftUpperCoefficient_add_lower_eq_zero, zero_smul]

/-- Once the two simplex-word comparisons are known, a positive inserted-right
upper face cancels its lower-boundary partner. -/
theorem shihRightBoundaryTerm_add_lower_eq_zero_of_maps
    (X Y : SimplicialObject C) (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2)) (hb : 0 < b.val)
    (hleft :
      X.map (ShihIndex.rightBoundaryUpperIndex p q m hm t b).leftHom.op ≫
          X.δ (ShihIndex.rightBoundaryUpperFace p q m t b) =
        X.δ (ShihIndex.rightBoundaryLowerFace p q m b hb) ≫
          X.map (ShihIndex.ofGap p q m hm t).leftHom.op)
    (hright :
      Y.map (ShihIndex.rightBoundaryUpperIndex p q m hm t b).rightHom.op ≫
          Y.δ (ShihIndex.rightBoundaryUpperFace p q m t b) =
        Y.δ (ShihIndex.rightBoundaryLowerFace p q m b hb) ≫
          Y.map (ShihIndex.ofGap p q m hm t).rightHom.op) :
    shihUpperBoundaryTerm X Y (p + q + m + 1)
        (ShihIndex.rightBoundaryUpperIndex p q m hm t b)
        (ShihIndex.rightBoundaryUpperFace p q m t b) +
      shihLowerBoundaryTerm X Y (p + q + m)
        (ShihIndex.rightBoundaryLowerFace p q m b hb)
        (ShihIndex.ofGap p q m hm t) = 0 := by
  unfold shihUpperBoundaryTerm shihLowerBoundaryTerm shihSummand
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    MonoidalCategory.tensorHom_comp_tensorHom]
  rw [hleft, hright]
  simp only [smul_smul]
  rw [← add_smul]
  change
    (ShihIndex.rightUpperCoefficient p q m hm t b +
      ShihIndex.rightLowerCoefficient p q m hm t b hb) • _ = 0
  rw [ShihIndex.rightUpperCoefficient_add_lower_eq_zero, zero_smul]

/-- The finite inserted-left interior family cancels after the two
simplex-word comparisons have been established pointwise. -/
theorem shihLeftBoundaryInterior_sum_eq_zero_of_maps
    (X Y : SimplicialObject C) (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q)
    (hleft : ∀ a : {a : Fin (p + 3) // 0 < a.val ∧ a.val < p + 2},
      X.map (ShihIndex.leftBoundaryUpperIndex p q m hm t a).leftHom.op ≫
          X.δ (ShihIndex.leftBoundaryUpperFace p q m t a) =
        X.δ (ShihIndex.leftBoundaryLowerFace p q m hm a a.2.1) ≫
          X.map (ShihIndex.ofGap p q m hm t).leftHom.op)
    (hright : ∀ a : {a : Fin (p + 3) // 0 < a.val ∧ a.val < p + 2},
      Y.map (ShihIndex.leftBoundaryUpperIndex p q m hm t a).rightHom.op ≫
          Y.δ (ShihIndex.leftBoundaryUpperFace p q m t a) =
        Y.δ (ShihIndex.leftBoundaryLowerFace p q m hm a a.2.1) ≫
          Y.map (ShihIndex.ofGap p q m hm t).rightHom.op) :
    (∑ a : {a : Fin (p + 3) // 0 < a.val ∧ a.val < p + 2},
        shihUpperBoundaryTerm X Y (p + q + m + 1)
          (ShihIndex.leftBoundaryUpperIndex p q m hm t a)
          (ShihIndex.leftBoundaryUpperFace p q m t a)) +
      ∑ a : {a : Fin (p + 3) // 0 < a.val ∧ a.val < p + 2},
        shihLowerBoundaryTerm X Y (p + q + m)
          (ShihIndex.leftBoundaryLowerFace p q m hm a a.2.1)
          (ShihIndex.ofGap p q m hm t) = 0 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun a _ =>
    shihLeftBoundaryTerm_add_lower_eq_zero_of_maps X Y p q m hm t a
      a.2.1 a.2.2 (hleft a) (hright a)

/-- The finite positive inserted-right family cancels after the two
simplex-word comparisons have been established pointwise. -/
theorem shihRightBoundaryPositive_sum_eq_zero_of_maps
    (X Y : SimplicialObject C) (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q)
    (hleft : ∀ b : {b : Fin (q + 2) // 0 < b.val},
      X.map (ShihIndex.rightBoundaryUpperIndex p q m hm t b).leftHom.op ≫
          X.δ (ShihIndex.rightBoundaryUpperFace p q m t b) =
        X.δ (ShihIndex.rightBoundaryLowerFace p q m b b.2) ≫
          X.map (ShihIndex.ofGap p q m hm t).leftHom.op)
    (hright : ∀ b : {b : Fin (q + 2) // 0 < b.val},
      Y.map (ShihIndex.rightBoundaryUpperIndex p q m hm t b).rightHom.op ≫
          Y.δ (ShihIndex.rightBoundaryUpperFace p q m t b) =
        Y.δ (ShihIndex.rightBoundaryLowerFace p q m b b.2) ≫
          Y.map (ShihIndex.ofGap p q m hm t).rightHom.op) :
    (∑ b : {b : Fin (q + 2) // 0 < b.val},
        shihUpperBoundaryTerm X Y (p + q + m + 1)
          (ShihIndex.rightBoundaryUpperIndex p q m hm t b)
          (ShihIndex.rightBoundaryUpperFace p q m t b)) +
      ∑ b : {b : Fin (q + 2) // 0 < b.val},
        shihLowerBoundaryTerm X Y (p + q + m)
          (ShihIndex.rightBoundaryLowerFace p q m b b.2)
          (ShihIndex.ofGap p q m hm t) = 0 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun b _ =>
    shihRightBoundaryTerm_add_lower_eq_zero_of_maps X Y p q m hm t b b.2
      (hleft b) (hright b)

end AlgebraicTopology.EilenbergZilber
