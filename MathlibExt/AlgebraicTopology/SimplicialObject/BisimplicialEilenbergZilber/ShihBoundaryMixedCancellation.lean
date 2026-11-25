/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihBoundaryExpansion
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryMixedCancellation

/-!
# Mixed active-face cancellation for the bisimplicial Shih boundary

Swapping adjacent mixed positions preserves both simplex words and reverses
the Shih sign.  Evaluating the two word equalities through
`Bisimplicial.map` gives pointwise cancellation, and the existing partner
involution then cancels the complete finite mixed family.
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

/-- Paired mixed active faces cancel pointwise. -/
theorem shihMixedActiveBoundaryTerm_add_partner_eq_zero
    {n : ℕ} (i : AlgebraicTopology.EilenbergZilber.ShihIndex n)
    (x : AlgebraicTopology.EilenbergZilber.Shuffle.MixedFace (i.p + 1) i.q)
    (hx : x.shuffle = i.shuffle) :
    shihUpperBoundaryTerm B n i (i.activeBoundaryFace x.faceIndex) +
      shihUpperBoundaryTerm B n
        (i.replaceShuffle x.partner.shuffle)
        (i.activeBoundaryFace x.partner.faceIndex) = 0 := by
  unfold shihUpperBoundaryTerm shihSummand shihMap
  simp only [Preadditive.zsmul_comp, smul_smul]
  have hd₁ :
      ((SimplicialObject.diagonalFunctor A).obj B).δ
          (i.activeBoundaryFace x.faceIndex) =
        AlgebraicTopology.Bisimplicial.map B
          (SimplexCategory.δ (i.activeBoundaryFace x.faceIndex))
          (SimplexCategory.δ (i.activeBoundaryFace x.faceIndex)) := by
    exact (AlgebraicTopology.Bisimplicial.map_diagonal B _).symm
  have hd₂ :
      ((SimplicialObject.diagonalFunctor A).obj B).δ
          (i.activeBoundaryFace x.partner.faceIndex) =
        AlgebraicTopology.Bisimplicial.map B
          (SimplexCategory.δ (i.activeBoundaryFace x.partner.faceIndex))
          (SimplexCategory.δ (i.activeBoundaryFace x.partner.faceIndex)) := by
    exact (AlgebraicTopology.Bisimplicial.map_diagonal B _).symm
  rw [hd₁, AlgebraicTopology.Bisimplicial.map_comp]
  rw [hd₂, AlgebraicTopology.Bisimplicial.map_comp]
  have hmap :
      AlgebraicTopology.Bisimplicial.map B
          (SimplexCategory.δ (i.activeBoundaryFace x.faceIndex) ≫ i.leftHom)
          (SimplexCategory.δ (i.activeBoundaryFace x.faceIndex) ≫ i.rightHom) =
        AlgebraicTopology.Bisimplicial.map B
          (SimplexCategory.δ (i.activeBoundaryFace x.partner.faceIndex) ≫
            (i.replaceShuffle x.partner.shuffle).leftHom)
          (SimplexCategory.δ (i.activeBoundaryFace x.partner.faceIndex) ≫
            (i.replaceShuffle x.partner.shuffle).rightHom) := by
    exact congrArg₂ (AlgebraicTopology.Bisimplicial.map B)
      (AlgebraicTopology.EilenbergZilber.delta_activeBoundaryFace_comp_leftHom_partner
        i x hx)
      (AlgebraicTopology.EilenbergZilber.delta_activeBoundaryFace_comp_rightHom_partner
        i x hx)
  rw [hmap, i.sign_replaceShuffle_partner x hx]
  simp only [AlgebraicTopology.EilenbergZilber.ShihIndex.activeBoundaryFace,
    AlgebraicTopology.EilenbergZilber.Shuffle.MixedFace.partner_faceIndex]
  rw [mul_neg, neg_smul, add_neg_cancel]

/-- For fixed bidegree and positive gap, the complete mixed active-face sum vanishes. -/
theorem shihMixedActiveBoundary_sum_eq_zero
    (p q m : ℕ) (hm : 0 < m) :
    ∑ x : AlgebraicTopology.EilenbergZilber.Shuffle.MixedFace (p + 1) q,
      shihUpperBoundaryTerm B (p + q + m)
        (AlgebraicTopology.EilenbergZilber.ShihIndex.ofGap p q m hm x.shuffle)
        (AlgebraicTopology.EilenbergZilber.ShihIndex.activeBoundaryFaceOfGap
          p q m hm x.faceIndex) = 0 := by
  apply Finset.sum_involution (fun x _ => x.partner)
  · intro x _
    have hcancel := shihMixedActiveBoundaryTerm_add_partner_eq_zero B
      (AlgebraicTopology.EilenbergZilber.ShihIndex.ofGap p q m hm x.shuffle) x rfl
    have hindex :
        (AlgebraicTopology.EilenbergZilber.ShihIndex.ofGap p q m hm x.shuffle).replaceShuffle
            x.partner.shuffle =
          AlgebraicTopology.EilenbergZilber.ShihIndex.ofGap p q m hm x.partner.shuffle := by
      rfl
    have hfirst :
        (AlgebraicTopology.EilenbergZilber.ShihIndex.ofGap p q m hm x.shuffle).activeBoundaryFace
            x.faceIndex =
          AlgebraicTopology.EilenbergZilber.ShihIndex.activeBoundaryFaceOfGap
            p q m hm x.faceIndex := by
      exact AlgebraicTopology.EilenbergZilber.ShihIndex.activeBoundaryFace_ofGap
        p q m hm x.shuffle x.faceIndex
    have hsecond :
        shihUpperBoundaryTerm B (p + q + m)
            ((AlgebraicTopology.EilenbergZilber.ShihIndex.ofGap
              p q m hm x.shuffle).replaceShuffle x.partner.shuffle)
            ((AlgebraicTopology.EilenbergZilber.ShihIndex.ofGap
              p q m hm x.shuffle).activeBoundaryFace x.partner.faceIndex) =
          shihUpperBoundaryTerm B (p + q + m)
            (AlgebraicTopology.EilenbergZilber.ShihIndex.ofGap
              p q m hm x.partner.shuffle)
            (AlgebraicTopology.EilenbergZilber.ShihIndex.activeBoundaryFaceOfGap
              p q m hm x.partner.faceIndex) := by
      rw [hindex]
      congr 1
    calc
      _ = shihUpperBoundaryTerm B (p + q + m)
            (AlgebraicTopology.EilenbergZilber.ShihIndex.ofGap
              p q m hm x.shuffle)
            ((AlgebraicTopology.EilenbergZilber.ShihIndex.ofGap
              p q m hm x.shuffle).activeBoundaryFace x.faceIndex) +
          shihUpperBoundaryTerm B (p + q + m)
            ((AlgebraicTopology.EilenbergZilber.ShihIndex.ofGap
              p q m hm x.shuffle).replaceShuffle x.partner.shuffle)
            ((AlgebraicTopology.EilenbergZilber.ShihIndex.ofGap
              p q m hm x.shuffle).activeBoundaryFace x.partner.faceIndex) := by
              rw [hfirst, hsecond]
      _ = 0 := hcancel
  · intro x _ _
    exact x.partner_ne
  · intro x _
    simp
  · intro x _
    simp

end AlgebraicTopology.BisimplicialEilenbergZilber
