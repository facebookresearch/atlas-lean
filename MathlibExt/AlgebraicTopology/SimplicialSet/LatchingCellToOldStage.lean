/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SkeletalCellOperatorGeometry
import MathlibExt.AlgebraicTopology.SimplicialSet.SkeletalUnionProductAttachment

/-!
# Latching and degeneracy cells in the preceding diagonal skeleton

Tensors of the whole outer latching subcomplex and its finite stages map into the preceding diagonal skeleton, with explicit equations after the skeletal inclusion. Degeneracy cells factor through these finite-stage maps and are natural in the simplicial diagram. Sharp row maps and the preceding stage invariant make the degeneracy-to-stage comparison a weak equivalence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkLatchingOldStage
open SharpComparisonDraft RezkSkeletalCell RezkSkeletalProduct RezkCompatiblePushout

/-- The actual whole latching coefficient cell enters the old skeleton
through its original union-product attachment inclusion. -/
def wholeToOld (X : SimplicialObject SSet.{u}) (n : ℕ) :
    (outerLatching X (n + 1) : SSet.{u}) ⊗ Δ[n + 1] ⟶ diagonalFiltration X n :=
  Subcomplex.unionProd.ι₂ (outerLatching X (n + 1)) (boundary (n + 1)) ≫
    diagonalAttachmentTopMap X n

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem wholeToOld_ι (X : SimplicialObject SSet.{u}) (n : ℕ) :
    wholeToOld X n ≫ (diagonalFiltration X n).ι =
      ((outerLatching X (n + 1)).ι ▷ Δ[n + 1]) ≫ diagonalCellMap X (n + 1) := by
  dsimp only [wholeToOld]
  rw [Category.assoc, diagonalAttachmentTopMap_ι]
  dsimp only [diagonalAttachmentDomain]
  rw [Subcomplex.unionProd.ι₂_ι_assoc]

/-- Every actual partial latching stage lies in the whole latching object. -/
theorem stage_le_whole (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStage X n r ≤ outerLatching X (n + 1) := by
  rw [outerLatching_succ_eq_iSup_range_sigma]
  unfold outerLatchingStage
  apply iSup_le
  intro j
  apply iSup_le
  intro hj
  exact le_iSup (fun j => Subcomplex.range (X.σ j)) j

/-- The SAME finite latching stage, with its original full simplex factor. -/
def stageToOld (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    (outerLatchingStage X n r : SSet.{u}) ⊗ Δ[n + 1] ⟶ diagonalFiltration X n :=
  (Subcomplex.homOfLE (stage_le_whole X n r) ▷ Δ[n + 1]) ≫ wholeToOld X n

@[reassoc]
theorem stageToOld_ι (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    stageToOld X n r ≫ (diagonalFiltration X n).ι =
      ((outerLatchingStage X n r).ι ▷ Δ[n + 1]) ≫ diagonalCellMap X (n + 1) := by
  dsimp only [stageToOld]
  rw [Category.assoc, wholeToOld_ι, ← Category.assoc,
    ← comp_whiskerRight, Subcomplex.homOfLE_ι]

/-- The original rth degeneracy cell enters the old stage through the
actual noninjective standard-simplex operator. -/
def degeneracyToOld (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    X.obj (op ⦋n⦌) ⊗ Δ[n + 1] ⟶ diagonalFiltration X n :=
  (X.obj (op ⦋n⦌) ◁ SSet.stdSimplex.map (SimplexCategory.σ r)) ≫ cellToStage X n n le_rfl

@[reassoc]
theorem degeneracyToOld_ι (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    degeneracyToOld X n r ≫ (diagonalFiltration X n).ι =
      (X.σ r ▷ Δ[n + 1]) ≫ diagonalCellMap X (n + 1) := by
  rw [degeneracyToOld, Category.assoc, cellToStage_ι]
  exact (diagonalCellMap_operator X (SimplexCategory.σ r)).symm

/-- Naturality retains the same old-stage map and coefficient degree n. -/
@[reassoc]
theorem degeneracyToOld_naturality {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    degeneracyToOld X n r ≫ diagonalFiltrationNatMap eta n =
      (eta.app (op ⦋n⦌) ▷ Δ[n + 1]) ≫ degeneracyToOld Y n r := by
  unfold degeneracyToOld
  rw [Category.assoc, cellToStage_naturality, ← Category.assoc, whisker_exchange]
  simp only [Category.assoc]

/-- All degeneracy pieces are incoming HC by strict tensor basechange and
the actual old cell assertion. No degeneracy HC is assumed. -/
theorem degeneracyToOld_hc {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ a : SimplexCategory, Sharp (eta.app (op a)))
    (n : ℕ) (r : Fin (n + 1)) (previous : stageCellInvariant eta n) :
    WeakEquivalence
      (pullback.lift (degeneracyToOld X n r) (eta.app (op ⦋n⦌) ▷ Δ[n + 1])
        (degeneracyToOld_naturality eta n r) ≫
        comparison (diagonalFiltrationNatMap eta n) (degeneracyToOld Y n r)) := by
  have first := tensor_boundary_hc (eta.app (op ⦋n⦌))
              (SSet.stdSimplex.map (SimplexCategory.σ r)) (hrows ⦋n⦌)
  have rectangle := (RezkIncomingHC.first_hc_iff_rectangle
    (X.obj (op ⦋n⦌) ◁ SSet.stdSimplex.map (SimplexCategory.σ r))
    (cellToStage X n n le_rfl)
    (eta.app (op ⦋n⦌) ▷ Δ[n + 1]) (eta.app (op ⦋n⦌) ▷ Δ[n])
    (diagonalFiltrationNatMap eta n)
    (Y.obj (op ⦋n⦌) ◁ SSet.stdSimplex.map (SimplexCategory.σ r))
    (cellToStage Y n n le_rfl)
    (whisker_exchange _ _) (cellToStage_naturality eta n n le_rfl)
    (tensor_map_sharp _ _ (hrows ⦋n⦌)) previous.1 (previous.2 n le_rfl)).mp first
  exact rectangle

/-- The original range-to-stage leg identifies the same degeneracy piece. -/
theorem degeneracy_stage_factor (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    (outerDegeneracyToLatchingStage X n r ▷ Δ[n + 1]) ≫ stageToOld X n r =
      degeneracyToOld X n r := by
  apply (cancel_mono (diagonalFiltration X n).ι).mp
  rw [Category.assoc, stageToOld_ι, degeneracyToOld_ι, ← Category.assoc,
    ← comp_whiskerRight, outerDegeneracyToLatchingStage_ι]

end SSet.RezkLatchingOldStage
