/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.DifferentialMaps

/-!
# The positive-bidegree bisimplicial shuffle differential

For positive bidegrees, expand a shuffle followed by the diagonal alternating
differential into shuffle-face pairs.  The existing mixed-face involution
cancels the mixed pairs.  The remaining left and right boundary faces
reassemble respectively into the outer and signed inner alternating
differentials followed by smaller shuffle maps.
-/

@[expose] public section

open CategoryTheory Simplicial SimplexCategory
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialEilenbergZilber

variable {A : Type u} [Category.{v} A] [Preadditive A]
  (B : SimplicialObject (SimplicialObject A))

private theorem shuffleBidegree_comp_objD_eq_boundary_sum_positive (p q : ℕ) :
    shuffleBidegree B (p + 1) (q + 1) ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD
          ((SimplicialObject.diagonalFunctor A).obj B) ((p + 1) + q) =
      ∑ z : AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) (q + 1) ×
          Fin ((p + 1) + (q + 1) + 1),
        ((-1 : ℤ) ^ z.2.val) •
          (shuffleSummand B z.1 ≫
            ((SimplicialObject.diagonalFunctor A).obj B).δ
              (n := (p + 1) + q) (Fin.cast (by omega) z.2)) := by
  unfold shuffleBidegree AlgebraicTopology.AlternatingFaceMapComplex.objD
  simp only [Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.comp_zsmul, Finset.smul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_product']
  apply Finset.sum_congr rfl
  intro z _
  rfl

private theorem shuffleBidegree_comp_objD_eq_signed_boundary_sum_positive
    (p q : ℕ) :
    shuffleBidegree B (p + 1) (q + 1) ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD
          ((SimplicialObject.diagonalFunctor A).obj B) ((p + 1) + q) =
      ∑ z : AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) (q + 1) ×
          Fin ((p + 1) + (q + 1) + 1),
        AlgebraicTopology.EilenbergZilber.shuffleSignZ z.1 •
          shuffleBoundaryTermPositive B p q z.1 z.2 := by
  rw [shuffleBidegree_comp_objD_eq_boundary_sum_positive]
  apply Finset.sum_congr rfl
  intro z _
  simp only [shuffleBoundaryTermPositive, diagonalBoundaryMapPositive,
    shuffleSummand, Preadditive.zsmul_comp, smul_smul]
  congr 1
  ring

private theorem shuffleBidegree_comp_objD_eq_nonmixed_sum_positive
    (p q : ℕ) :
    shuffleBidegree B (p + 1) (q + 1) ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD
          ((SimplicialObject.diagonalFunctor A).obj B) ((p + 1) + q) =
      ∑ z ∈ AlgebraicTopology.EilenbergZilber.Shuffle.nonmixedBoundaryFaces
          (p + 1) (q + 1),
        AlgebraicTopology.EilenbergZilber.shuffleSignZ z.1 •
          shuffleBoundaryTermPositive B p q z.1 z.2 := by
  rw [shuffleBidegree_comp_objD_eq_signed_boundary_sum_positive]
  exact AlgebraicTopology.EilenbergZilber.Shuffle.sum_boundary_eq_sum_nonmixedBoundaryFaces
    (shuffleBoundaryTermPositive B p q) (shuffleBoundaryTermPositive_partner B p q)

private theorem shuffleBidegree_comp_objD_eq_boundary_sums_positive
    (p q : ℕ) :
    shuffleBidegree B (p + 1) (q + 1) ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD
          ((SimplicialObject.diagonalFunctor A).obj B) ((p + 1) + q) =
      (∑ x : Fin (p + 2) ×
          AlgebraicTopology.EilenbergZilber.Shuffle p (q + 1),
        AlgebraicTopology.EilenbergZilber.shuffleSignZ
            (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryPair x).1 •
          shuffleBoundaryTermPositive B p q
            (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryPair x).1
            (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryPair x).2) +
      (∑ x : Fin (q + 2) ×
          AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) q,
        AlgebraicTopology.EilenbergZilber.shuffleSignZ
            (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryPair x).1 •
          shuffleBoundaryTermPositive B p q
            (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryPair x).1
            (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryPair x).2) := by
  rw [shuffleBidegree_comp_objD_eq_nonmixed_sum_positive]
  exact AlgebraicTopology.EilenbergZilber.Shuffle.sum_nonmixedBoundaryFaces_positive
    (fun s i => AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
      shuffleBoundaryTermPositive B p q s i)

/-- In positive bidegrees, the shuffle followed by the diagonal alternating
differential is the outer differential followed by the smaller shuffle plus
the signed inner differential followed by the smaller shuffle. -/
theorem shuffleBidegree_comp_objD_positive (p q : ℕ) :
    shuffleBidegree B (p + 1) (q + 1) ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD
          ((SimplicialObject.diagonalFunctor A).obj B) ((p + 1) + q) =
      ((AlgebraicTopology.AlternatingFaceMapComplex.objD B p).app
          (Opposite.op ⦋q + 1⦌) ≫
        shuffleBidegree B p (q + 1) ≫
        (eqToHom (by rw [show p + (q + 1) = (p + 1) + q by omega]) :
          (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
              (p + (q + 1)) ⟶
            (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
              ((p + 1) + q))) +
      ((-1 : ℤ) ^ (p + 1)) •
        (AlgebraicTopology.AlternatingFaceMapComplex.objD
            (B.obj (Opposite.op ⦋p + 1⦌)) q ≫
          shuffleBidegree B (p + 1) q) := by
  rw [shuffleBidegree_comp_objD_eq_boundary_sums_positive]
  congr 1
  · rw [Fintype.sum_prod_type]
    simp_rw [AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryPair,
      shuffleBoundaryTermPositive_leftBoundary]
    unfold AlgebraicTopology.AlternatingFaceMapComplex.objD shuffleBidegree shuffleSummand
    simp only [NatTrans.app_sum, NatTrans.app_zsmul,
      Preadditive.sum_comp, Preadditive.comp_sum,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul,
      Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    ring
  · rw [Fintype.sum_prod_type]
    simp_rw [AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryPair,
      shuffleBoundaryTermPositive_rightBoundary]
    unfold AlgebraicTopology.AlternatingFaceMapComplex.objD shuffleBidegree shuffleSummand
    simp only [Preadditive.sum_comp, Preadditive.comp_sum,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul,
      Finset.smul_sum, pow_add]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    ring

end AlgebraicTopology.BisimplicialEilenbergZilber
