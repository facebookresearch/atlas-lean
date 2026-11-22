/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FibrationCharacterization
import MathlibExt.CategoryTheory.MorphismProperty.OverCells

/-!
# Genuine small testing families over the original marked base

Each cell is indexed by every actual whole map of its target to the
maximally marked base. Native local Hom smallness keeps this enlarged
index small in the original value universe. Its right class is exactly
the underlying small cell right class. For a quasicategory base, lifting
the actual terminal map in the over category detects precisely the
original intrinsically marked Cartesian or cocartesian fibrations.
No marked model, accessibility or factorization outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace SSet.Marked

/-- The actual original Cartesian cells over all their supplied whole base maps. -/
def cartesianCellsOver (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  MorphismProperty.overCells cartesianCell.{u} (max B)

/-- The corresponding original cocartesian cells in the same over category. -/
def cocartesianCellsOver (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  MorphismProperty.overCells cocartesianCell.{u} (max B)

/-- The Cartesian base-indexed testing family is genuinely small at the original value universe. -/
theorem cartesianCellsOver_isSmall (B : SSet.{u}) :
    MorphismProperty.IsSmall.{u} (cartesianCellsOver B) := by
  let _ : Small.{u} FibrationCellIndex := fibrationCellIndex_small
  exact MorphismProperty.overCells_isSmall _ _

/-- The same exact smallness holds for the original cocartesian family. -/
theorem cocartesianCellsOver_isSmall (B : SSet.{u}) :
    MorphismProperty.IsSmall.{u} (cocartesianCellsOver B) := by
  let _ : Small.{u} FibrationCellIndex := fibrationCellIndex_small
  exact MorphismProperty.overCells_isSmall _ _

/-- Every original Cartesian over-cell is a genuine marked monomorphism in the over category. -/
theorem cartesianCellsOver_le_monomorphisms (B : SSet.{u}) :
    cartesianCellsOver B ≤ MorphismProperty.monomorphisms (Over (max B)) :=
  MorphismProperty.overCells_le_monomorphisms _ _ cartesianCell_mono

/-- The same original monomorphism property holds for the cocartesian over-cells. -/
theorem cocartesianCellsOver_le_monomorphisms (B : SSet.{u}) :
    cocartesianCellsOver B ≤ MorphismProperty.monomorphisms (Over (max B)) :=
  MorphismProperty.overCells_le_monomorphisms _ _ cocartesianCell_mono

/-- The whole native slice lifting condition is exactly the underlying Cartesian cell lifting condition. -/
theorem cartesianCellsOver_rlp_iff {B : SSet.{u}} {X Y : Over (max B)} (p : X ⟶ Y) :
    (cartesianCellsOver B).rlp p ↔ cartesianCells.{u}.rlp p.left :=
  MorphismProperty.overCells_rlp_iff _ _ p

/-- Native cocartesian lifting in the slice has the same precise underlying meaning. -/
theorem cocartesianCellsOver_rlp_iff {B : SSet.{u}} {X Y : Over (max B)} (p : X ⟶ Y) :
    (cocartesianCellsOver B).rlp p ↔ cocartesianCells.{u}.rlp p.left :=
  MorphismProperty.overCells_rlp_iff _ _ p

/-- The native terminal over-map lifts the small cells exactly for the original intrinsically marked
  Cartesian fibrations. -/
theorem cartesianCellsOver_terminal_rlp_iff {B : SSet.{u}} [Quasicategory B]
    (X : Over (max B)) :
    (cartesianCellsOver B).rlp (Over.mkIdTerminal.from X) ↔ cartesianObjects B X := by
  rw [cartesianCellsOver_rlp_iff]
  have hleft : (Over.mkIdTerminal.from X).left = X.hom := by
    exact Over.mkIdTerminal_from_left X
  rw [hleft]
  exact cartesianCells_rlp_iff_cartesianObjects X.hom

/-- The actual small terminal lifting class is precisely the native cocartesian fibration and its supplied
  intrinsic marking. -/
theorem cocartesianCellsOver_terminal_rlp_iff {B : SSet.{u}} [Quasicategory B]
    (X : Over (max B)) :
    (cocartesianCellsOver B).rlp (Over.mkIdTerminal.from X) ↔ cocartesianObjects B X := by
  rw [cocartesianCellsOver_rlp_iff]
  have hleft : (Over.mkIdTerminal.from X).left = X.hom := by
    exact Over.mkIdTerminal_from_left X
  rw [hleft]
  exact cocartesianCells_rlp_iff_cocartesianObjects X.hom

end SSet.Marked
