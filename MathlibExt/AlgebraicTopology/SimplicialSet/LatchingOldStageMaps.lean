/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.LatchingCellToOldStage
import MathlibExt.AlgebraicTopology.SimplicialSet.LatchingSourceOverlapRowHC

/-!
# Natural finite latching maps into diagonal skeleta

Finite latching stages, their preceding pieces, and degeneracy source overlaps map naturally into the preceding diagonal skeleton, preserving the cell inclusion equations. For sharp row maps with weak relative comparisons for every simplex operator, the preceding stage invariant makes the source-overlap-to-skeleton comparison a weak equivalence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkLatchingOldStage
open SharpComparisonDraft RezkSkeletalCell RezkSkeletalProduct

@[reassoc]
theorem stageToOld_naturality {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    stageToOld X n r ≫ diagonalFiltrationNatMap eta n =
      (outerLatchingStageMap eta n r ▷ Δ[n + 1]) ≫ stageToOld Y n r := by
  apply (cancel_mono (diagonalFiltration Y n).ι).mp
  simp only [Category.assoc, diagonalFiltrationNatMap_ι, stageToOld_ι_assoc, stageToOld_ι]
  rw [← diagonalCellMap_naturality]
  simp only [tensorHom_id, ← Category.assoc, ← comp_whiskerRight, outerLatchingStageMap_ι]

/-- The original before-stage map factors through the same current finite stage. -/
def beforeToOld (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    (outerLatchingStageBefore X n r : SSet.{u}) ⊗ Δ[n + 1] ⟶ diagonalFiltration X n :=
  (Subcomplex.homOfLE (by rw [outerLatchingStage_eq_before_sup_range]; exact le_sup_left)
      ▷ Δ[n + 1]) ≫
    stageToOld X n r

@[reassoc]
theorem beforeToOld_ι (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    beforeToOld X n r ≫ (diagonalFiltration X n).ι =
      ((outerLatchingStageBefore X n r).ι ▷ Δ[n + 1]) ≫ diagonalCellMap X (n + 1) := by
  dsimp only [beforeToOld]
  rw [Category.assoc, stageToOld_ι, ← Category.assoc,
    ← comp_whiskerRight, Subcomplex.homOfLE_ι]

@[reassoc]
theorem beforeToOld_naturality {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    beforeToOld X n r ≫ diagonalFiltrationNatMap eta n =
      (outerLatchingStageBeforeMap eta n r ▷ Δ[n + 1]) ≫ beforeToOld Y n r := by
  apply (cancel_mono (diagonalFiltration Y n).ι).mp
  simp only [Category.assoc, diagonalFiltrationNatMap_ι, beforeToOld_ι_assoc, beforeToOld_ι]
  rw [← diagonalCellMap_naturality]
  simp only [tensorHom_id, ← Category.assoc, ← comp_whiskerRight, outerLatchingStageBeforeMap_ι]

/-- The actual source overlap enters the old stage through the same
degeneracy cell. This retains the source preimage, not merely its image. -/
def sourceOverlapToOld (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    (outerLatchingStageSourceOverlap X n r : SSet.{u}) ⊗ Δ[n + 1] ⟶ diagonalFiltration X n :=
  ((outerLatchingStageSourceOverlap X n r).ι ▷ Δ[n + 1]) ≫ degeneracyToOld X n r

@[reassoc]
theorem sourceOverlapToOld_naturality {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    sourceOverlapToOld X n r ≫ diagonalFiltrationNatMap eta n =
      (outerLatchingStageSourceOverlapMap eta n r ▷ Δ[n + 1]) ≫ sourceOverlapToOld Y n r := by
  unfold sourceOverlapToOld
  rw [Category.assoc, degeneracyToOld_naturality]
  simp only [← Category.assoc, ← comp_whiskerRight, outerLatchingStageSourceOverlapMap_ι]

/-- Incoming HC of the actual source overlap is derived from the finite
row-overlap proof and the actual degeneracy-to-old-stage HC. -/
theorem sourceOverlapToOld_hc {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ a : SimplexCategory, Sharp (eta.app (op a)))
    (hoperators : ∀ {a b : SimplexCategory} (f : a ⟶ b),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f))
    (n : ℕ) (r : Fin (n + 1)) (previous : stageCellInvariant eta n) :
    WeakEquivalence
      (pullback.lift (sourceOverlapToOld X n r)
        (outerLatchingStageSourceOverlapMap eta n r ▷ Δ[n + 1])
        (sourceOverlapToOld_naturality eta n r) ≫
        comparison (diagonalFiltrationNatMap eta n) (sourceOverlapToOld Y n r)) := by
  let square : CommSq (outerLatchingStageSourceOverlap X n r).ι
      (outerLatchingStageSourceOverlapMap eta n r) (eta.app (op ⦋n⦌))
      (outerLatchingStageSourceOverlap Y n r).ι :=
    CommSq.mk (outerLatchingStageSourceOverlapMap_ι eta n r).symm
  have first := finite_tensor_hc square (hrows ⦋n⦌)
    (RezkSourceOverlapIncoming.source_overlap_row_hc eta hrows hoperators n r)
    (K := (Δ[n + 1] : SSet.{u}))
  exact (RezkIncomingHC.first_hc_iff_rectangle
    ((outerLatchingStageSourceOverlap X n r).ι ▷ Δ[n + 1]) (degeneracyToOld X n r)
    (outerLatchingStageSourceOverlapMap eta n r ▷ Δ[n + 1]) (eta.app (op ⦋n⦌) ▷ Δ[n + 1])
    (diagonalFiltrationNatMap eta n)
    ((outerLatchingStageSourceOverlap Y n r).ι ▷ Δ[n + 1]) (degeneracyToOld Y n r)
    (by simp only [← comp_whiskerRight, outerLatchingStageSourceOverlapMap_ι])
    (degeneracyToOld_naturality eta n r) (tensor_map_sharp _ _ (hrows ⦋n⦌))
    previous.1 (degeneracyToOld_hc eta hrows n r previous)).mp first

end SSet.RezkLatchingOldStage
