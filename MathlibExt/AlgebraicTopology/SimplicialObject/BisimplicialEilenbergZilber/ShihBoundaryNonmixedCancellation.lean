/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihBoundaryExpansion
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryNonmixedMapsLeft
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryNonmixedMapsRight
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryEndpointCancellation
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryLeftEdgeCancellation

/-!
# Nonmixed cancellations for the bisimplicial Shih boundary

The existing Shih development proves the required pairs of simplex-word
equalities and all coefficient identities.  This file evaluates each pair by
`Bisimplicial.map`, proving the interior left/right cancellations and the
transition, endpoint, and left-edge cancellations without duplicating their
combinatorics.
-/

@[expose] public section

open CategoryTheory Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialEilenbergZilber

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [Category.{v} A] [Preadditive A]
  (B : SimplicialObject (SimplicialObject A))

private theorem shihUpperBoundaryTerm_add_eq_zero_of_words
    {n : ℕ}
    (i j : AlgebraicTopology.EilenbergZilber.ShihIndex n)
    (k l : Fin (n + 2))
    (hleft : SimplexCategory.δ k ≫ i.leftHom =
      SimplexCategory.δ l ≫ j.leftHom)
    (hright : SimplexCategory.δ k ≫ i.rightHom =
      SimplexCategory.δ l ≫ j.rightHom)
    (hcoeff : ((-1 : ℤ) ^ k.val) * i.sign +
      ((-1 : ℤ) ^ l.val) * j.sign = 0) :
    shihUpperBoundaryTerm B n i k + shihUpperBoundaryTerm B n j l = 0 := by
  unfold shihUpperBoundaryTerm shihSummand shihMap
  simp only [Preadditive.zsmul_comp, smul_smul]
  have hdk :
      ((SimplicialObject.diagonalFunctor A).obj B).δ k =
        AlgebraicTopology.Bisimplicial.map B
          (SimplexCategory.δ k) (SimplexCategory.δ k) := by
    exact (AlgebraicTopology.Bisimplicial.map_diagonal B _).symm
  have hdl :
      ((SimplicialObject.diagonalFunctor A).obj B).δ l =
        AlgebraicTopology.Bisimplicial.map B
          (SimplexCategory.δ l) (SimplexCategory.δ l) := by
    exact (AlgebraicTopology.Bisimplicial.map_diagonal B _).symm
  rw [hdk, AlgebraicTopology.Bisimplicial.map_comp]
  rw [hdl, AlgebraicTopology.Bisimplicial.map_comp]
  rw [congrArg₂ (AlgebraicTopology.Bisimplicial.map B) hleft hright]
  rw [← add_smul, hcoeff, zero_smul]

/-- An interior inserted-left upper face cancels its lower-boundary partner. -/
theorem shihLeftBoundaryTerm_add_lower_eq_zero
    (p q m : ℕ) (hm : 0 < m)
    (t : AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) q)
    (a : Fin (p + 3)) (ha0 : 0 < a.val) (haLast : a.val < p + 2) :
    shihUpperBoundaryTerm B (p + q + m + 1)
        (AlgebraicTopology.EilenbergZilber.ShihIndex.leftBoundaryUpperIndex
          p q m hm t a)
        (AlgebraicTopology.EilenbergZilber.ShihIndex.leftBoundaryUpperFace
          p q m t a) +
      shihLowerBoundaryTerm B (p + q + m)
        (AlgebraicTopology.EilenbergZilber.ShihIndex.leftBoundaryLowerFace
          p q m hm a ha0)
        (AlgebraicTopology.EilenbergZilber.ShihIndex.ofGap p q m hm t) = 0 := by
  unfold shihUpperBoundaryTerm shihLowerBoundaryTerm shihSummand shihMap
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul]
  have hdUpper :
      ((SimplicialObject.diagonalFunctor A).obj B).δ
          (AlgebraicTopology.EilenbergZilber.ShihIndex.leftBoundaryUpperFace
            p q m t a) =
        AlgebraicTopology.Bisimplicial.map B
          (SimplexCategory.δ
            (AlgebraicTopology.EilenbergZilber.ShihIndex.leftBoundaryUpperFace
              p q m t a))
          (SimplexCategory.δ
            (AlgebraicTopology.EilenbergZilber.ShihIndex.leftBoundaryUpperFace
              p q m t a)) := by
    exact (AlgebraicTopology.Bisimplicial.map_diagonal B _).symm
  have hdLower :
      ((SimplicialObject.diagonalFunctor A).obj B).δ
          (AlgebraicTopology.EilenbergZilber.ShihIndex.leftBoundaryLowerFace
            p q m hm a ha0) =
        AlgebraicTopology.Bisimplicial.map B
          (SimplexCategory.δ
            (AlgebraicTopology.EilenbergZilber.ShihIndex.leftBoundaryLowerFace
              p q m hm a ha0))
          (SimplexCategory.δ
            (AlgebraicTopology.EilenbergZilber.ShihIndex.leftBoundaryLowerFace
              p q m hm a ha0)) := by
    exact (AlgebraicTopology.Bisimplicial.map_diagonal B _).symm
  rw [hdUpper, AlgebraicTopology.Bisimplicial.map_comp]
  rw [hdLower, AlgebraicTopology.Bisimplicial.map_comp]
  have hleftOp := AlgebraicTopology.EilenbergZilber.ShihIndex.leftBoundaryUpper_leftWord
    p q m hm t a ha0
  have hrightOp := AlgebraicTopology.EilenbergZilber.ShihIndex.leftBoundaryUpper_rightWord
    p q m hm t a ha0 haLast
  have hleft := congrArg Quiver.Hom.unop hleftOp
  have hright := congrArg Quiver.Hom.unop hrightOp
  simp only [CategoryTheory.unop_comp, Quiver.Hom.unop_op] at hleft hright
  have hmap := congrArg₂ (AlgebraicTopology.Bisimplicial.map B) hleft hright
  rw [hmap]
  rw [← add_smul]
  change
    (AlgebraicTopology.EilenbergZilber.ShihIndex.leftUpperCoefficient
        p q m hm t a +
      AlgebraicTopology.EilenbergZilber.ShihIndex.leftLowerCoefficient
        p q m hm t a ha0) • _ = 0
  rw [AlgebraicTopology.EilenbergZilber.ShihIndex.leftUpperCoefficient_add_lower_eq_zero,
    zero_smul]

/-- A positive inserted-right upper face cancels its lower-boundary partner. -/
theorem shihRightBoundaryTerm_add_lower_eq_zero
    (p q m : ℕ) (hm : 0 < m)
    (t : AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) q)
    (b : Fin (q + 2)) (hb : 0 < b.val) :
    shihUpperBoundaryTerm B (p + q + m + 1)
        (AlgebraicTopology.EilenbergZilber.ShihIndex.rightBoundaryUpperIndex
          p q m hm t b)
        (AlgebraicTopology.EilenbergZilber.ShihIndex.rightBoundaryUpperFace
          p q m t b) +
      shihLowerBoundaryTerm B (p + q + m)
        (AlgebraicTopology.EilenbergZilber.ShihIndex.rightBoundaryLowerFace
          p q m b hb)
        (AlgebraicTopology.EilenbergZilber.ShihIndex.ofGap p q m hm t) = 0 := by
  unfold shihUpperBoundaryTerm shihLowerBoundaryTerm shihSummand shihMap
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul]
  have hdUpper :
      ((SimplicialObject.diagonalFunctor A).obj B).δ
          (AlgebraicTopology.EilenbergZilber.ShihIndex.rightBoundaryUpperFace
            p q m t b) =
        AlgebraicTopology.Bisimplicial.map B
          (SimplexCategory.δ
            (AlgebraicTopology.EilenbergZilber.ShihIndex.rightBoundaryUpperFace
              p q m t b))
          (SimplexCategory.δ
            (AlgebraicTopology.EilenbergZilber.ShihIndex.rightBoundaryUpperFace
              p q m t b)) := by
    exact (AlgebraicTopology.Bisimplicial.map_diagonal B _).symm
  have hdLower :
      ((SimplicialObject.diagonalFunctor A).obj B).δ
          (AlgebraicTopology.EilenbergZilber.ShihIndex.rightBoundaryLowerFace
            p q m b hb) =
        AlgebraicTopology.Bisimplicial.map B
          (SimplexCategory.δ
            (AlgebraicTopology.EilenbergZilber.ShihIndex.rightBoundaryLowerFace
              p q m b hb))
          (SimplexCategory.δ
            (AlgebraicTopology.EilenbergZilber.ShihIndex.rightBoundaryLowerFace
              p q m b hb)) := by
    exact (AlgebraicTopology.Bisimplicial.map_diagonal B _).symm
  rw [hdUpper, AlgebraicTopology.Bisimplicial.map_comp]
  rw [hdLower, AlgebraicTopology.Bisimplicial.map_comp]
  have hleftOp := AlgebraicTopology.EilenbergZilber.ShihIndex.rightBoundaryUpper_leftWord
    p q m hm t b hb
  have hrightOp := AlgebraicTopology.EilenbergZilber.ShihIndex.rightBoundaryUpper_rightWord
    p q m hm t b hb
  have hleft := congrArg Quiver.Hom.unop hleftOp
  have hright := congrArg Quiver.Hom.unop hrightOp
  simp only [CategoryTheory.unop_comp, Quiver.Hom.unop_op] at hleft hright
  have hmap := congrArg₂ (AlgebraicTopology.Bisimplicial.map B) hleft hright
  rw [hmap]
  rw [← add_smul]
  change
    (AlgebraicTopology.EilenbergZilber.ShihIndex.rightUpperCoefficient
        p q m hm t b +
      AlgebraicTopology.EilenbergZilber.ShihIndex.rightLowerCoefficient
        p q m hm t b hb) • _ = 0
  rw [AlgebraicTopology.EilenbergZilber.ShihIndex.rightUpperCoefficient_add_lower_eq_zero,
    zero_smul]

/-- The finite inserted-left interior family cancels. -/
theorem shihLeftBoundaryInterior_sum_eq_zero
    (p q m : ℕ) (hm : 0 < m)
    (t : AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) q) :
    (∑ a : {a : Fin (p + 3) // 0 < a.val ∧ a.val < p + 2},
        shihUpperBoundaryTerm B (p + q + m + 1)
          (AlgebraicTopology.EilenbergZilber.ShihIndex.leftBoundaryUpperIndex
            p q m hm t a)
          (AlgebraicTopology.EilenbergZilber.ShihIndex.leftBoundaryUpperFace
            p q m t a)) +
      ∑ a : {a : Fin (p + 3) // 0 < a.val ∧ a.val < p + 2},
        shihLowerBoundaryTerm B (p + q + m)
          (AlgebraicTopology.EilenbergZilber.ShihIndex.leftBoundaryLowerFace
            p q m hm a a.2.1)
          (AlgebraicTopology.EilenbergZilber.ShihIndex.ofGap p q m hm t) = 0 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun a _ =>
    shihLeftBoundaryTerm_add_lower_eq_zero B p q m hm t a a.2.1 a.2.2

/-- The finite positive inserted-right family cancels. -/
theorem shihRightBoundaryPositive_sum_eq_zero
    (p q m : ℕ) (hm : 0 < m)
    (t : AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) q) :
    (∑ b : {b : Fin (q + 2) // 0 < b.val},
        shihUpperBoundaryTerm B (p + q + m + 1)
          (AlgebraicTopology.EilenbergZilber.ShihIndex.rightBoundaryUpperIndex
            p q m hm t b)
          (AlgebraicTopology.EilenbergZilber.ShihIndex.rightBoundaryUpperFace
            p q m t b)) +
      ∑ b : {b : Fin (q + 2) // 0 < b.val},
        shihLowerBoundaryTerm B (p + q + m)
          (AlgebraicTopology.EilenbergZilber.ShihIndex.rightBoundaryLowerFace
            p q m b b.2)
          (AlgebraicTopology.EilenbergZilber.ShihIndex.ofGap p q m hm t) = 0 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun b _ =>
    shihRightBoundaryTerm_add_lower_eq_zero B p q m hm t b b.2

/-- A transition face cancels the active face from a zero left insertion. -/
theorem shihTransitionBoundaryTerm_add_leftZero_eq_zero
    (p q m : ℕ) (hm : 0 < m)
    (t : AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) q) :
    shihUpperBoundaryTerm B (p + q + m + 1)
          (AlgebraicTopology.EilenbergZilber.ShihIndex.ofGap
            p q (m + 1) (by omega) t)
          (AlgebraicTopology.EilenbergZilber.ShihIndex.transitionUpperFace p q m) +
      shihUpperBoundaryTerm B (p + q + m + 1)
          (AlgebraicTopology.EilenbergZilber.ShihIndex.leftBoundaryUpperIndex
            p q m hm t 0)
          (AlgebraicTopology.EilenbergZilber.ShihIndex.leftBoundaryUpperFace
            p q m t 0) = 0 := by
  have hc :=
    AlgebraicTopology.EilenbergZilber.ShihIndex.transitionCoefficient_add_leftZero_eq_zero
      p q m hm t
  unfold AlgebraicTopology.EilenbergZilber.ShihIndex.leftUpperCoefficient at hc
  exact shihUpperBoundaryTerm_add_eq_zero_of_words B _ _ _ _
    (AlgebraicTopology.EilenbergZilber.ShihIndex.delta_transition_comp_leftHom_eq_leftZero
      p q m hm t)
    (AlgebraicTopology.EilenbergZilber.ShihIndex.delta_transition_comp_rightHom_eq_leftZero
      p q m hm t) hc

/-- The final left insertion cancels the zero right insertion. -/
theorem shihLeftLastBoundaryTerm_add_rightZero_eq_zero
    (p q m : ℕ) (hm : 0 < m)
    (t : AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) q) :
    shihUpperBoundaryTerm B (p + q + m + 1)
          (AlgebraicTopology.EilenbergZilber.ShihIndex.leftBoundaryUpperIndex
            p q m hm t (Fin.last (p + 2)))
          (AlgebraicTopology.EilenbergZilber.ShihIndex.leftBoundaryUpperFace
            p q m t (Fin.last (p + 2))) +
      shihUpperBoundaryTerm B (p + q + m + 1)
          (AlgebraicTopology.EilenbergZilber.ShihIndex.rightBoundaryUpperIndex
            p q m hm t 0)
          (AlgebraicTopology.EilenbergZilber.ShihIndex.rightBoundaryUpperFace
            p q m t 0) = 0 := by
  have hc :=
    AlgebraicTopology.EilenbergZilber.ShihIndex.leftLastCoefficient_add_rightZero_eq_zero
      p q m hm t
  unfold AlgebraicTopology.EilenbergZilber.ShihIndex.leftUpperCoefficient
    AlgebraicTopology.EilenbergZilber.ShihIndex.rightUpperCoefficient at hc
  exact shihUpperBoundaryTerm_add_eq_zero_of_words B _ _ _ _
    (AlgebraicTopology.EilenbergZilber.ShihIndex.delta_leftLast_comp_leftHom_eq_rightZero
      p q m hm t)
    (AlgebraicTopology.EilenbergZilber.ShihIndex.delta_leftLast_comp_rightHom_eq_rightZero
      p q m hm t) hc

/-- Consecutive last/zero left-edge terms cancel. -/
theorem shihLeftEdge_last_add_zeroSucc_eq_zero
    (n : ℕ) (q : Fin n) :
    shihUpperBoundaryTerm B (n + 1)
        (AlgebraicTopology.EilenbergZilber.ShihIndex.leftEdgeIndex
          (n + 1) q.castSucc (Fin.last 1))
        (AlgebraicTopology.EilenbergZilber.ShihIndex.leftEdgeFace
          (n + 1) q.castSucc (Fin.last 1)) +
      shihUpperBoundaryTerm B (n + 1)
        (AlgebraicTopology.EilenbergZilber.ShihIndex.leftEdgeIndex
          (n + 1) q.succ 0)
        (AlgebraicTopology.EilenbergZilber.ShihIndex.leftEdgeFace
          (n + 1) q.succ 0) = 0 := by
  have hc :
      ((-1 : ℤ) ^ (AlgebraicTopology.EilenbergZilber.ShihIndex.leftEdgeFace
          (n + 1) q.castSucc (Fin.last 1)).val) *
          (AlgebraicTopology.EilenbergZilber.ShihIndex.leftEdgeIndex
            (n + 1) q.castSucc (Fin.last 1)).sign +
        ((-1 : ℤ) ^ (AlgebraicTopology.EilenbergZilber.ShihIndex.leftEdgeFace
          (n + 1) q.succ 0).val) *
          (AlgebraicTopology.EilenbergZilber.ShihIndex.leftEdgeIndex
            (n + 1) q.succ 0).sign = 0 := by
    change
      AlgebraicTopology.EilenbergZilber.ShihIndex.leftEdgeCoefficient
          (n + 1) q.castSucc (Fin.last 1) +
        AlgebraicTopology.EilenbergZilber.ShihIndex.leftEdgeCoefficient
          (n + 1) q.succ 0 = 0
    rw [AlgebraicTopology.EilenbergZilber.ShihIndex.leftEdgeCoefficient_last,
      AlgebraicTopology.EilenbergZilber.ShihIndex.leftEdgeCoefficient_zero]
    norm_num
  exact shihUpperBoundaryTerm_add_eq_zero_of_words B _ _ _ _
    (AlgebraicTopology.EilenbergZilber.ShihIndex.delta_leftEdgeLast_comp_leftHom_eq_zeroSucc
      n q)
    (AlgebraicTopology.EilenbergZilber.ShihIndex.delta_leftEdgeLast_comp_rightHom_eq_zeroSucc
      n q) hc

end AlgebraicTopology.BisimplicialEilenbergZilber
