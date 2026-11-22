/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverFibrationCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CylinderCompletedCells

/-!
# Actual small fixed-base horn/mono cells

Retain every original auxiliary cell over all its whole target maps to the
base. Add the native fixed-base parameter horn corners of the original
marked mono generators in that same slice. Their base map factors through
the original source projection. These are distinct from lifting both
absolute cylinder endpoints over arbitrary parameter-to-base maps.
Smallness includes every actual target-to-base Hom, and monicity is
proved on the original native pushout-product.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty
open scoped Simplicial

namespace SSet.Marked

/-- Every original marked mono generator with every actual whole map of its target to the base. -/
abbrev FixedBaseMonoIndex (B : SSet.{u}) := OverCellIndex monoCell.{u} (max B)

/-- Positive-dimensional original Kan horns retain their actual horn index. -/
abbrev FixedBaseHornIndex := Σ n : ℕ, Fin (n + 2)

/-- The original marked mono over the supplied whole base map. -/
def fixedBaseMonoCell (B : SSet.{u}) (s : FixedBaseMonoIndex B) : Arrow (Over (max B)) :=
  Arrow.mk (overCell monoCell (max B) s)

/-- Its whole original underlying marked map is unchanged. -/
@[simp]
theorem fixedBaseMonoCell_left (B : SSet.{u}) (s : FixedBaseMonoIndex B) :
    (fixedBaseMonoCell B s).hom.left = (monoCell.{u} s.1).hom := rfl

/-- The original fixed-base mono cell is genuinely monic. -/
theorem fixedBaseMonoCell_mono (B : SSet.{u}) (s : FixedBaseMonoIndex B) : Mono (fixedBaseMonoCell B s).hom := by
  let _ : Mono (monoCell.{u} s.1).hom := monoCell_mono s.1
  let _ : Mono (overCell monoCell (max B) s).left := monoCell_mono s.1
  change Mono (overCell monoCell (max B) s)
  exact Over.mono_of_mono_left _

/-- The original constant-base parameter horn corner on the actual marked mono generator. -/
def fixedBaseHornCell (B : SSet.{u}) (s : FixedBaseMonoIndex B × FixedBaseHornIndex) : Arrow (Over (max B)) :=
  Arrow.mk (overParameterPushoutProduct (horn.{u} (s.2.1 + 1) s.2.2).ι (fixedBaseMonoCell B s.1).hom)

/-- The original native full corner remains monic. -/
theorem fixedBaseHornCell_mono (B : SSet.{u}) (s : FixedBaseMonoIndex B × FixedBaseHornIndex) :
    Mono (fixedBaseHornCell B s).hom := by
  let _ : Mono (fixedBaseMonoCell B s.1).hom := fixedBaseMonoCell_mono B s.1
  exact overParameterHorn_mono _ _ _

/-- The complete original mono/base-map index is small in the original value universe. -/
theorem fixedBaseMonoIndex_small (B : SSet.{u}) : Small.{u} (FixedBaseMonoIndex B) := by
  let _ : Small.{u} MonoCellIndex := small_zero _
  let _ (s : MonoCellIndex) : Small.{u} ((monoCell.{u} s).right ⟶ max B) :=
    (inferInstance : LocallySmall.{u} Marked.{u}).hom_small _ _
  infer_instance

/-- The original auxiliary whole-base indices and fixed-base horn corners share this actual family index. -/
abbrev FixedBaseCellIndex (a : FibrationCellIndex → Arrow Marked.{u}) (B : SSet.{u}) :=
  OverCellIndex a (max B) ⊕ (FixedBaseMonoIndex B × FixedBaseHornIndex)

/-- Every actual whole auxiliary target-to-base map and positive horn corner is small at the original universe. -/
theorem fixedBaseCellIndex_small (a : FibrationCellIndex → Arrow Marked.{u}) (B : SSet.{u}) :
    Small.{u} (FixedBaseCellIndex a B) := by
  let _ : Small.{u} FibrationCellIndex := fibrationCellIndex_small
  let _ (s : FibrationCellIndex) : Small.{u} ((a s).right ⟶ max B) :=
    (inferInstance : LocallySmall.{u} Marked.{u}).hom_small _ _
  let _ : Small.{u} (FixedBaseMonoIndex B) := fixedBaseMonoIndex_small B
  let _ : Small.{u} FixedBaseHornIndex := small_zero _
  infer_instance

/-- The actual cartesian auxiliary cells and native constant-base mono/horn corners. -/
def cartesianFixedBaseCell (B : SSet.{u}) (s : FixedBaseCellIndex cartesianCell.{u} B) : Arrow (Over (max B)) :=
  match s with
  | .inl s => Arrow.mk (overCell cartesianCell (max B) s)
  | .inr s => fixedBaseHornCell B s

/-- The actual original cartesian fixed-base generating property. -/
def cartesianFixedBaseCells (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  ofHoms (fun s => (cartesianFixedBaseCell B s).hom)

/-- Every actual cartesian fixed-base cell is monic, including its complete original markings. -/
theorem cartesianFixedBaseCell_mono (B : SSet.{u}) (s : FixedBaseCellIndex cartesianCell.{u} B) :
    Mono (cartesianFixedBaseCell B s).hom := by
  cases s with
  | inl s =>
    let _ : Mono (overCell cartesianCell (max B) s).left := cartesianCell_mono s.1
    change Mono (overCell cartesianCell (max B) s)
    exact Over.mono_of_mono_left _
  | inr s => exact fixedBaseHornCell_mono B s

/-- All actual cartesian fixed-base cells belong to the original mono class. -/
theorem cartesianFixedBaseCells_le_monomorphisms (B : SSet.{u}) :
    cartesianFixedBaseCells B ≤ monomorphisms (Over (max B)) := by
  rintro A D f ⟨s⟩
  exact cartesianFixedBaseCell_mono B s

/-- This actual cartesian family is genuinely small in the original value universe. -/
theorem cartesianFixedBaseCells_isSmall (B : SSet.{u}) : IsSmall.{u} (cartesianFixedBaseCells B) := by
  let _ : Small.{u} (FixedBaseCellIndex cartesianCell.{u} B) := fixedBaseCellIndex_small _ B
  exact isSmall_ofHoms _

/-- Every original cartesian auxiliary cell is retained with its same whole base map. -/
theorem cartesianCellsOver_le_fixedBase (B : SSet.{u}) : cartesianCellsOver B ≤ cartesianFixedBaseCells B := by
  rintro A D f ⟨s⟩
  exact ofHoms.mk (f := fun s => (cartesianFixedBaseCell B s).hom) (.inl s)

/-- The actual cocartesian auxiliary cells and native constant-base mono/horn corners. -/
def cocartesianFixedBaseCell (B : SSet.{u}) (s : FixedBaseCellIndex cocartesianCell.{u} B) : Arrow (Over (max B)) :=
  match s with
  | .inl s => Arrow.mk (overCell cocartesianCell (max B) s)
  | .inr s => fixedBaseHornCell B s

/-- The actual original cocartesian fixed-base generating property. -/
def cocartesianFixedBaseCells (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  ofHoms (fun s => (cocartesianFixedBaseCell B s).hom)

/-- Every actual cocartesian fixed-base cell is monic, including its complete original markings. -/
theorem cocartesianFixedBaseCell_mono (B : SSet.{u}) (s : FixedBaseCellIndex cocartesianCell.{u} B) :
    Mono (cocartesianFixedBaseCell B s).hom := by
  cases s with
  | inl s =>
    let _ : Mono (overCell cocartesianCell (max B) s).left := cocartesianCell_mono s.1
    change Mono (overCell cocartesianCell (max B) s)
    exact Over.mono_of_mono_left _
  | inr s => exact fixedBaseHornCell_mono B s

/-- All actual cocartesian fixed-base cells belong to the original mono class. -/
theorem cocartesianFixedBaseCells_le_monomorphisms (B : SSet.{u}) :
    cocartesianFixedBaseCells B ≤ monomorphisms (Over (max B)) := by
  rintro A D f ⟨s⟩
  exact cocartesianFixedBaseCell_mono B s

/-- This actual cocartesian family is genuinely small in the original value universe. -/
theorem cocartesianFixedBaseCells_isSmall (B : SSet.{u}) : IsSmall.{u} (cocartesianFixedBaseCells B) := by
  let _ : Small.{u} (FixedBaseCellIndex cocartesianCell.{u} B) := fixedBaseCellIndex_small _ B
  exact isSmall_ofHoms _

/-- Every original cocartesian auxiliary cell is retained with its same whole base map. -/
theorem cocartesianCellsOver_le_fixedBase (B : SSet.{u}) : cocartesianCellsOver B ≤ cocartesianFixedBaseCells B := by
  rintro A D f ⟨s⟩
  exact ofHoms.mk (f := fun s => (cocartesianFixedBaseCell B s).hom) (.inl s)

end SSet.Marked
