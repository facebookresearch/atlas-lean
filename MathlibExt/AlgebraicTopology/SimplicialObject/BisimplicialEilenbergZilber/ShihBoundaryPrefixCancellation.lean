/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihBoundaryExpansion
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryPrefixCancellation

/-!
# Prefix-face cancellation for the bisimplicial Shih boundary

An upper face strictly before the active Shih block is paired with the same
face for the lower index obtained by shortening the inactive prefix.  The two
simplex words agree in both directions and the Shih sign reverses.
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

/-- A paired upper/lower prefix-face contribution cancels pointwise. -/
theorem shihPrefixBoundaryTerm_add_eq_zero
    {n : ℕ} (i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1))
    (k : Fin (n + 3)) (hk : k.val + 1 < i.gap) :
    shihUpperBoundaryTerm B (n + 1) i k +
      shihLowerBoundaryTerm B n (i.lowerPrefixFace k hk)
        (i.lowerPrefix (by omega)) = 0 := by
  unfold shihUpperBoundaryTerm shihLowerBoundaryTerm shihSummand shihMap
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul]
  have hdk :
      ((SimplicialObject.diagonalFunctor A).obj B).δ k =
        AlgebraicTopology.Bisimplicial.map B
          (SimplexCategory.δ k) (SimplexCategory.δ k) := by
    exact (AlgebraicTopology.Bisimplicial.map_diagonal B _).symm
  have hdl :
      ((SimplicialObject.diagonalFunctor A).obj B).δ
          (i.lowerPrefixFace k hk) =
        AlgebraicTopology.Bisimplicial.map B
          (SimplexCategory.δ (i.lowerPrefixFace k hk))
          (SimplexCategory.δ (i.lowerPrefixFace k hk)) := by
    exact (AlgebraicTopology.Bisimplicial.map_diagonal B _).symm
  rw [hdk, AlgebraicTopology.Bisimplicial.map_comp]
  rw [hdl, AlgebraicTopology.Bisimplicial.map_comp]
  have hmap := congrArg₂ (AlgebraicTopology.Bisimplicial.map B)
    (AlgebraicTopology.EilenbergZilber.delta_comp_leftHom_lowerPrefix i k hk)
    (AlgebraicTopology.EilenbergZilber.delta_comp_rightHom_lowerPrefix i k hk)
  rw [hmap, AlgebraicTopology.EilenbergZilber.ShihIndex.sign_lowerPrefix]
  simp only [AlgebraicTopology.EilenbergZilber.ShihIndex.lowerPrefixFace,
    mul_neg, neg_smul, add_neg_cancel]

/-- All upper and lower faces strictly before the active block cancel under
the canonical prefix-removal equivalence. -/
theorem shihPrefixBoundary_sum_eq_zero (n : ℕ) :
    (∑ z : AlgebraicTopology.EilenbergZilber.ShihUpperPrefixIndex n,
        shihUpperBoundaryTerm B (n + 1) z.val.2 z.val.1) +
      ∑ z : AlgebraicTopology.EilenbergZilber.ShihLowerPrefixIndex n,
        shihLowerBoundaryTerm B n z.val.2 z.val.1 = 0 := by
  rw [← (AlgebraicTopology.EilenbergZilber.shihUpperPrefixEquivLowerPrefix n).sum_comp
    (fun z => shihLowerBoundaryTerm B n z.val.2 z.val.1)]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun z _ =>
    shihPrefixBoundaryTerm_add_eq_zero B z.val.2 z.val.1 z.property

end AlgebraicTopology.BisimplicialEilenbergZilber
