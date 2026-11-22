/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeHomotopyTestingAccessibility
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeHomotopyTestingSaturation
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Smith

/-!
# Genuine uniform all-arrow Smith recognition for relative homotopy testing

The original marked slice is locally presentable, its actual mono
sources have a proved common rank, and the full relative homotopy weak
class and its inclusion are now proved accessible. Native lifting theory
proves weak-mono saturation and mono-right weakness. Beke--Smith therefore
produces the actual small weak-mono generating family, both genuine WFS
and both reverse class equalities for this same all-arrow homotopy class.
Its identification with the full intrinsic mapping weak class remains a
separate obligation; no supplied model or solution-set result is used.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace SSet.Marked

/-- The whole original mono family has a genuine small-object argument from its proved actual source bounds. -/
theorem fixedBaseMonoCells_hasSmallObjectArgument (B : SSet.{u}) :
    (overCells monoCell.{u} (max B)).HasSmallObjectArgument.{u} := by
  let _ : Small.{u} (FixedBaseMonoIndex B) := fixedBaseMonoIndex_small B
  obtain ⟨κ, hκ, hX⟩ := exists_fixedBaseMono_source_target_cardinal B
  let _ : Fact κ.IsRegular := hκ
  let _ (s : FixedBaseMonoIndex B) : IsCardinalPresentable (fixedBaseMonoCell B s).left κ := (hX s).1
  exact ofHoms_hasSmallObjectArgument_atCardinal (fun s => (fixedBaseMonoCell B s).hom) κ

/-- The same original small mono family has exactly the full native mono-right lifting class. -/
theorem fixedBaseMonoCells_rlp_eq (B : SSet.{u}) :
    (overCells monoCell.{u} (max B)).rlp = (monomorphisms (Over (max B))).rlp := by
  ext X Y p
  exact fixedBaseMonoCells_rlp_iff p

/-- Its native full left class is exactly the original marked slice monomorphisms. -/
theorem fixedBaseMonoCells_left_eq (B : SSet.{u}) :
    (overCells monoCell.{u} (max B)).rlp.llp = monomorphisms (Over (max B)) := by
  rw [fixedBaseMonoCells_rlp_eq]
  exact (CellSmallness.over_mono_isWeakFactorizationSystem B).llp

/-- Native mono-right maps pass all original Cartesian relative homotopy tests. -/
theorem monoRight_le_cartesianRelativeHomotopyTesting (B : SSet.{u}) [Quasicategory B] :
    (monomorphisms (Over (max B))).rlp ≤ cartesianRelativeHomotopyTesting B := by
  let _ := relativeIntervalCylinder_isExact (max B)
  let _ := cartesianRelativeBoundary_isAnodyneSystem B
  let _ : InitialMonoClass (Over (max B)) := over_initialMonoClass (max B)
  exact (relativeIntervalCylinder (max B)).rlp_monomorphisms_le_testingEquivalences
    (cartesianRelativeBoundaryCells B).rlp.llp

/-- The same whole original mono-right class is weak for the dual relative homotopy tests. -/
theorem monoRight_le_cocartesianRelativeHomotopyTesting (B : SSet.{u}) [Quasicategory B] :
    (monomorphisms (Over (max B))).rlp ≤ cocartesianRelativeHomotopyTesting B := by
  let _ := relativeIntervalCylinder_isExact (max B)
  let _ := cocartesianRelativeBoundary_isAnodyneSystem B
  let _ : InitialMonoClass (Over (max B)) := over_initialMonoClass (max B)
  exact (relativeIntervalCylinder (max B)).rlp_monomorphisms_le_testingEquivalences
    (cocartesianRelativeBoundaryCells B).rlp.llp

/-- Actual all-arrow Cartesian relative homotopy testing has a produced small generating family, both native
  WFS and both reverse recognition equalities. -/
theorem cartesianRelativeSmithRecognition (B : SSet.{u}) [Quasicategory B] :
    Nonempty (SmithModelStructureData.{u} (C := Over (max B))
      (overCells monoCell.{u} (max B)) (cartesianRelativeHomotopyTesting B)) := by
  let I := overCells monoCell.{u} (max B)
  let W := cartesianRelativeHomotopyTesting B
  let _ : IsLocallyPresentable.{u} (Over (max B)) := over_isLocallyPresentable (max B)
  let _ : I.HasSmallObjectArgument.{u} := fixedBaseMonoCells_hasSmallObjectArgument B
  let _ : W.IsAccessible.{u} := cartesianRelativeHomotopyTesting_isAccessible B
  have hCof : I.rlp.llp ⊓ W = cartesianRelativeHomotopyWeakMonos B := by rw [fixedBaseMonoCells_left_eq]; rfl
  apply smithRecognition_of_accessible I W
  · exact Precylinder.testingEquivalences.hasTwoOutOfThreeProperty _ _
  · exact Precylinder.testingEquivalences.isStableUnderRetracts _ _
  · rw [fixedBaseMonoCells_rlp_eq]
    exact monoRight_le_cartesianRelativeHomotopyTesting B
  · rw [hCof]
    exact cartesianRelativeHomotopyWeakMonos_cobase B
  · rw [hCof]
    exact cartesianRelativeHomotopyWeakMonos_transfinite B

/-- The genuine dual all-original-arrow construction likewise produces its small family and complete native
  class compatibility. -/
theorem cocartesianRelativeSmithRecognition (B : SSet.{u}) [Quasicategory B] :
    Nonempty (SmithModelStructureData.{u} (C := Over (max B))
      (overCells monoCell.{u} (max B)) (cocartesianRelativeHomotopyTesting B)) := by
  let I := overCells monoCell.{u} (max B)
  let W := cocartesianRelativeHomotopyTesting B
  let _ : IsLocallyPresentable.{u} (Over (max B)) := over_isLocallyPresentable (max B)
  let _ : I.HasSmallObjectArgument.{u} := fixedBaseMonoCells_hasSmallObjectArgument B
  let _ : W.IsAccessible.{u} := cocartesianRelativeHomotopyTesting_isAccessible B
  have hCof : I.rlp.llp ⊓ W = cocartesianRelativeHomotopyWeakMonos B := by rw [fixedBaseMonoCells_left_eq]; rfl
  apply smithRecognition_of_accessible I W
  · exact Precylinder.testingEquivalences.hasTwoOutOfThreeProperty _ _
  · exact Precylinder.testingEquivalences.isStableUnderRetracts _ _
  · rw [fixedBaseMonoCells_rlp_eq]
    exact monoRight_le_cocartesianRelativeHomotopyTesting B
  · rw [hCof]
    exact cocartesianRelativeHomotopyWeakMonos_cobase B
  · rw [hCof]
    exact cocartesianRelativeHomotopyWeakMonos_transfinite B

end SSet.Marked
