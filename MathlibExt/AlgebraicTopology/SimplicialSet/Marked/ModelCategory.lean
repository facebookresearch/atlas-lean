/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.UniformWeakTesting
import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRecognition
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# The genuine original fixed-base Cartesian and cocartesian marked models

Both actual native WFS and their full original class compatibility have
been proved from genuine source presentability, accessibility, testing
reduction and Smith recognition. The cofibrations are exactly the
original marked monos; weak equivalences are exactly the full intrinsic
relative mapping weak classes; fibrations are their actual weak-mono
right classes. Native model axioms now follow with no supplied outcomes.

The base is an arbitrary original quasicategory, including non-Kan
bases, and the value universe is unchanged. These named model choices
register no global instances. Marked straightening/unstraightening and
higher-height model comparisons are not asserted here.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace SSet.Marked

/-- The actual original marked slice cofibration structure is precisely its full marked-monomorphism class. -/
@[instance_reducible]
def markedCofibrationStructure (Z : Marked.{u}) : CategoryWithCofibrations (Over Z) :=
  ⟨monomorphisms (Over Z)⟩

/-- The original Cartesian full weak-mono right class gives this named fibration structure. -/
@[instance_reducible]
def cartesianMarkedFibrationStructure (B : SSet.{u}) : CategoryWithFibrations (Over (max B)) :=
  ⟨cartesianTestingFibrations B⟩

/-- The actual Cartesian weak structure retains precisely the original full intrinsic mapping tests. -/
@[instance_reducible]
def cartesianMarkedWeakStructure (B : SSet.{u}) : CategoryWithWeakEquivalences (Over (max B)) :=
  ⟨cartesianWeakEquivalences B⟩

/-- The original dual full weak-mono right class gives its same named fibration structure. -/
@[instance_reducible]
def cocartesianMarkedFibrationStructure (B : SSet.{u}) : CategoryWithFibrations (Over (max B)) :=
  ⟨cocartesianTestingFibrations B⟩

/-- The genuine dual weak class retains all original intrinsic cocartesian relative mapping tests. -/
@[instance_reducible]
def cocartesianMarkedWeakStructure (B : SSet.{u}) : CategoryWithWeakEquivalences (Over (max B)) :=
  ⟨cocartesianWeakEquivalences B⟩

/-- All actual fixed-base Cartesian marked model axioms hold for the exact original classes and arbitrary
  original quasicategory base. -/
@[instance_reducible]
def cartesianMarkedModelCategory (B : SSet.{u}) [Quasicategory B] :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    ModelCategory (Over (max B)) := by
  let _ := markedCofibrationStructure (max B)
  let _ := cartesianMarkedFibrationStructure B
  let _ := cartesianMarkedWeakStructure B
  exact (cartesianMarkedSmithData B).modelCategory (cartesianWeakEquivalences_hasTwoOutOfThreeProperty B)
    (fixedBaseMonoCells_left_eq B).symm (cartesianMarkedWeakCells_right_eq B).symm rfl

/-- The same original marked carrier has its genuine cocartesian model with the exact full dual weak and
  lifting classes. -/
@[instance_reducible]
def cocartesianMarkedModelCategory (B : SSet.{u}) [Quasicategory B] :
    let _ := markedCofibrationStructure (max B)
    let _ := cocartesianMarkedFibrationStructure B
    let _ := cocartesianMarkedWeakStructure B
    ModelCategory (Over (max B)) := by
  let _ := markedCofibrationStructure (max B)
  let _ := cocartesianMarkedFibrationStructure B
  let _ := cocartesianMarkedWeakStructure B
  exact (cocartesianMarkedSmithData B).modelCategory (cocartesianWeakEquivalences_hasTwoOutOfThreeProperty B)
    (fixedBaseMonoCells_left_eq B).symm (cocartesianMarkedWeakCells_right_eq B).symm rfl

/-- The original Cartesian marked model fibrant objects are EXACTLY the original intrinsic Cartesian
  fibrations with their complete intrinsic mark sets. -/
theorem cartesianMarkedModel_fibrant_iff (B : SSet.{u}) [Quasicategory B] (Y : Over (max B)) :
    let _ := cartesianMarkedFibrationStructure B
    IsFibrant Y ↔ cartesianObjects B Y := by
  let _ := cartesianMarkedFibrationStructure B
  dsimp only
  rw [isFibrant_iff, fibration_iff]
  change cartesianTestingFibrations B (terminal.from Y) ↔ _
  let _ : (cartesianTestingFibrations B).RespectsIso := by unfold cartesianTestingFibrations; infer_instance
  exact ((cartesianTestingFibrations B).arrow_iso_iff (relativeChosenTerminalArrowIso Y)).trans
    (cartesianTesting_terminal_iff_intrinsic Y)

/-- The dual model fibrancy retains precisely the original cocartesian projection and whole original
  intrinsic marking. -/
theorem cocartesianMarkedModel_fibrant_iff (B : SSet.{u}) [Quasicategory B] (Y : Over (max B)) :
    let _ := cocartesianMarkedFibrationStructure B
    IsFibrant Y ↔ cocartesianObjects B Y := by
  let _ := cocartesianMarkedFibrationStructure B
  dsimp only
  rw [isFibrant_iff, fibration_iff]
  change cocartesianTestingFibrations B (terminal.from Y) ↔ _
  let _ : (cocartesianTestingFibrations B).RespectsIso := by unfold cocartesianTestingFibrations; infer_instance
  exact ((cocartesianTestingFibrations B).arrow_iso_iff (relativeChosenTerminalArrowIso Y)).trans
    (cocartesianTesting_terminal_iff_intrinsic Y)

/-- Every arbitrary original marked slice object is genuinely cofibrant for its native marked-mono
  cofibration structure. -/
theorem markedCofibrationStructure_all_cofibrant (Z : Marked.{u}) (X : Over Z) :
    let _ := markedCofibrationStructure Z
    IsCofibrant X := by
  let _ := markedCofibrationStructure Z
  let _ : InitialMonoClass (Over Z) := over_initialMonoClass Z
  rw [isCofibrant_iff, cofibration_iff]
  change Mono (initial.to X)
  infer_instance

/-- The actual original Cartesian model has precisely marked monos as cofibrations and all original
  weak-mono lifts as fibrations. -/
theorem cartesianMarkedModel_classes (B : SSet.{u}) :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    cofibrations (Over (max B)) = monomorphisms (Over (max B)) ∧
      fibrations (Over (max B)) = cartesianTestingFibrations B ∧
      weakEquivalences (Over (max B)) = cartesianWeakEquivalences B := ⟨rfl, rfl, rfl⟩

/-- The same literal class readbacks hold for the native dual marked model choice. -/
theorem cocartesianMarkedModel_classes (B : SSet.{u}) :
    let _ := markedCofibrationStructure (max B)
    let _ := cocartesianMarkedFibrationStructure B
    let _ := cocartesianMarkedWeakStructure B
    cofibrations (Over (max B)) = monomorphisms (Over (max B)) ∧
      fibrations (Over (max B)) = cocartesianTestingFibrations B ∧
      weakEquivalences (Over (max B)) = cocartesianWeakEquivalences B := ⟨rfl, rfl, rfl⟩

end SSet.Marked
