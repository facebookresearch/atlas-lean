/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridMixedQSquare
public import MathlibExt.CategoryTheory.Waldhausen.ExactCategoryFunctor
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenMixedRealizationMap

/-!
# The actual independent-role original grid-to-Stage square

Original grid projection and weak-Stage reindex/functor laws derive the literal
lifted Stage square on every original chain. The original minimum-world
realization charts return it to the actual original mixed Waldhausen Stage map.
No root, inverse, triangle or diagonal-square outcome is supplied by the caller.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open scoped Simplicial Topology

universe uC vC uD vD

namespace AlgebraicKTheory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- Standard Waldhausen structure selected locally for the source exact category. -/
local instance originalMixedStageSquareWaldhausenC : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C
/-- Standard Waldhausen structure selected locally for the target exact category. -/
local instance originalMixedStageSquareWaldhausenD : WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

private theorem originalGridStageChainSquareComputed
    (n : SimplexCategoryᵒᵖ) (q : (quillenStageGridDiagonal C).obj n) :
    (quillenStageGridToStageWeakDiagonal (C := D)).app n
        (q ⋙ quillenStageGridLiftMap F n.unop) =
      ((quillenStageGridToStageWeakDiagonal (C := C)).app n q) ⋙
        (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).mapStageWeak n.unop.len := by
  let α := SimplexCategory.edgewiseRightInclusion.app n.unop
  have hStage := (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).mapStageWeak_reindex α
  have hGrid := quillenStageGridLiftMap_gridProjection F n.unop
  change (q ⋙ quillenStageGridLiftMap F n.unop ⋙
      quillenStageGridProjection D n.unop) ⋙ reindexStageWeak D α =
    (q ⋙ quillenStageGridProjection C n.unop ⋙ reindexStageWeak C α) ⋙
      (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).mapStageWeak n.unop.len
  have hProjection : q ⋙ quillenStageGridLiftMap F n.unop ⋙
      quillenStageGridProjection D n.unop =
      q ⋙ quillenStageGridProjection C n.unop ⋙
        (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).mapStageWeak
          (SimplexCategory.edgewiseQ.obj n.unop).len := by
    have h := congrArg (fun G => q ⋙ G) hGrid
    exact h
  exact (congrArg (fun G => G ⋙ reindexStageWeak D α) hProjection).trans
    (congrArg (fun G => q ⋙ quillenStageGridProjection C n.unop ⋙ G) hStage.symm)

private theorem originalGridStageCarrierSquareComputed :
    quillenStageGridDiagonalMixedMap F ≫
        SSet.uliftFunctor.{max uC vC, max uD vD}.map
          (quillenStageGridToStageWeakDiagonal (C := D)) =
      SSet.uliftFunctor.{max uD vD, max uC vC}.map
          (quillenStageGridToStageWeakDiagonal (C := C)) ≫
        (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalMixedMap := by
  apply NatTrans.ext
  funext n
  ext q
  apply ULift.ext
  change ((SSet.uliftFunctor.{max uC vC, max uD vD}.map
    (quillenStageGridToStageWeakDiagonal (C := D))).app n
      ((quillenStageGridDiagonalMixedMap F).app n q)).down =
    ((CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalMixedMap.app n
      ((SSet.uliftFunctor.{max uD vD, max uC vC}.map
        (quillenStageGridToStageWeakDiagonal (C := C))).app n q)).down
  rw [quillenStageGridDiagonalMixedMap_app,
    CategoryTheory.Functor.IsWaldhausenExact.stageWeakDiagonalMixedMap_app]
  change (quillenStageGridToStageWeakDiagonal (C := D)).app n
    (q.down ⋙ quillenStageGridLiftMap F n.unop) =
    ((quillenStageGridToStageWeakDiagonal (C := C)).app n q.down) ⋙
      (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).mapStageWeak n.unop.len
  exact originalGridStageChainSquareComputed F n q.down

/-- The literal original lifted grid/Stage chain square is derived internally
from original exact-functor/grid/reindex laws, in four independent category roles. -/
theorem quillenStageGridToStage_carrierLift_square :
    quillenStageGridDiagonalMixedMap F ≫
        SSet.uliftFunctor.{max uC vC, max uD vD}.map
          (quillenStageGridToStageWeakDiagonal (C := D)) =
      SSet.uliftFunctor.{max uD vD, max uC vC}.map
          (quillenStageGridToStageWeakDiagonal (C := C)) ≫
        (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalMixedMap :=
  originalGridStageCarrierSquareComputed F

private theorem originalStageMixedRealizationEqComputed :
    SSet.originalMixedRealization
      (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalMixedMap =
      (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap := by
  apply ContinuousMap.ext
  intro x
  exact (SSet.originalMixedRealization_apply
    (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalMixedMap x).trans
      ((CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap_apply x).symm

private theorem originalGridMixedRealizationEqForStageComputed :
    SSet.originalMixedRealization (quillenStageGridDiagonalMixedMap F) =
      quillenStageGridDiagonalRealMixedMap F := by
  apply ContinuousMap.ext
  intro x
  exact (SSet.originalMixedRealization_apply (quillenStageGridDiagonalMixedMap F) x).trans
    (quillenStageGridDiagonalRealMixedMap_apply F x).symm

/-- The ENTIRE original mixed grid-to-Stage realization square commutes with
the ACTUAL original mixed Stage map of the same primitive additive exact functor.
No triangle/root/inverse/coherence outcome is a caller hypothesis. -/
theorem quillenStageGridToStage_mixed_realization_square :
    (SSet.toTop.map (quillenStageGridToStageWeakDiagonal (C := D))).hom.comp
        (quillenStageGridDiagonalRealMixedMap F) =
      ((CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap).comp
        (SSet.toTop.map (quillenStageGridToStageWeakDiagonal (C := C))).hom := by
  have h := SSet.originalMixedRealization_square
    (quillenStageGridDiagonalMixedMap F)
    (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalMixedMap
    (quillenStageGridToStageWeakDiagonal (C := C))
    (quillenStageGridToStageWeakDiagonal (C := D))
    (quillenStageGridToStage_carrierLift_square F)
  rw [originalGridMixedRealizationEqForStageComputed F,
    originalStageMixedRealizationEqComputed F] at h
  exact h

end AlgebraicKTheory

end
