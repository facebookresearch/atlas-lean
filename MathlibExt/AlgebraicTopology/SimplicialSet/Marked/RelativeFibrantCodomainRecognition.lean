/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeAnodyneSystem
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverInitialMonomorphisms
import MathlibExt.AlgebraicTopology.ModelCategory.NaiveWeakTrivialFibrations

/-!
# Actual relative homotopy testing and fibrant-codomain reverse recognition

The genuine small anodyne system has exactly the original intrinsic
terminal targets. Native Cisinski deformation recognition applies to its
same original right maps with those intrinsic codomains. It produces the
whole strict section and relative cylinder homotopy and identifies their
homotopy testing weakness with right lifting against all original monos.
The full mapping weak class comparison and arbitrary-codomain model
recognition remain separate obligations.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace SSet.Marked

/-- The chosen categorical terminal arrow and the original identity-base terminal arrow retain the same
  source and native terminal comparison. -/
def relativeChosenTerminalArrowIso {Z : Marked.{u}} (Y : Over Z) :
    Arrow.mk (terminal.from Y) ≅ Arrow.mk (Over.mkIdTerminal.from Y) :=
  Arrow.isoMk (Iso.refl _) (Over.mkIdTerminal.uniqueUpToIso terminalIsTerminal).symm
    (Over.mkIdTerminal.hom_ext _ _)

/-- The genuine relative Cartesian anodyne system has exactly the original intrinsic naive fibrant objects. -/
theorem cartesianRelativeBoundary_naiveFibrant_iff {B : SSet.{u}} [Quasicategory B]
    (Y : Over (max B)) :
    (cartesianRelativeBoundaryCells B).rlp.llp.naiveFibrantObjects Y ↔ cartesianObjects B Y := by
  change (cartesianRelativeBoundaryCells B).rlp.llp.rlp (terminal.from Y) ↔ _
  rw [rlp_llp_rlp]
  exact ((cartesianRelativeBoundaryCells B).rlp.arrow_iso_iff (relativeChosenTerminalArrowIso Y)).trans
    (cartesianRelativeBoundary_terminal_iff_intrinsic Y)

/-- The same original dual small system has exactly the full original cocartesian terminal targets. -/
theorem cocartesianRelativeBoundary_naiveFibrant_iff {B : SSet.{u}} [Quasicategory B]
    (Y : Over (max B)) :
    (cocartesianRelativeBoundaryCells B).rlp.llp.naiveFibrantObjects Y ↔ cocartesianObjects B Y := by
  change (cocartesianRelativeBoundaryCells B).rlp.llp.rlp (terminal.from Y) ↔ _
  rw [rlp_llp_rlp]
  exact ((cocartesianRelativeBoundaryCells B).rlp.arrow_iso_iff (relativeChosenTerminalArrowIso Y)).trans
    (cocartesianRelativeBoundary_terminal_iff_intrinsic Y)

/-- The actual original relative-cylinder homotopy-class testing property for the proved Cartesian anodyne system. -/
def cartesianRelativeHomotopyTesting (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  (relativeIntervalCylinder (max B)).testingEquivalences (cartesianRelativeBoundaryCells B).rlp.llp

/-- The same original fixed-base cylinder testing class for the genuine dual anodyne system. -/
def cocartesianRelativeHomotopyTesting (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  (relativeIntervalCylinder (max B)).testingEquivalences (cocartesianRelativeBoundaryCells B).rlp.llp

/-- The full original Cartesian homotopy testing ranges over all original intrinsic targets, not a bounded
  replacement surrogate. -/
theorem cartesianRelativeHomotopyTesting_iff {B : SSet.{u}} [Quasicategory B]
    {X Y : Over (max B)} (f : X ⟶ Y) :
    cartesianRelativeHomotopyTesting B f ↔
      ∀ T : Over (max B), cartesianObjects B T →
        Function.Bijective ((relativeIntervalCylinder (max B)).homotopyClassPrecomp f T) := by
  constructor
  · intro h T hT
    exact h T ((cartesianRelativeBoundary_naiveFibrant_iff T).mpr hT)
  · intro h T hT
    exact h T ((cartesianRelativeBoundary_naiveFibrant_iff T).mp hT)

/-- The same all-target interpretation retains every original cocartesian target and native homotopy class. -/
theorem cocartesianRelativeHomotopyTesting_iff {B : SSet.{u}} [Quasicategory B]
    {X Y : Over (max B)} (f : X ⟶ Y) :
    cocartesianRelativeHomotopyTesting B f ↔
      ∀ T : Over (max B), cocartesianObjects B T →
        Function.Bijective ((relativeIntervalCylinder (max B)).homotopyClassPrecomp f T) := by
  constructor
  · intro h T hT
    exact h T ((cocartesianRelativeBoundary_naiveFibrant_iff T).mpr hT)
  · intro h T hT
    exact h T ((cocartesianRelativeBoundary_naiveFibrant_iff T).mp hT)

/-- An actual completed Cartesian right map with its original intrinsic codomain is homotopy testing weak
  exactly when it lifts every original mono. -/
theorem cartesianRelativeRight_testing_iff_monoRight {B : SSet.{u}} [Quasicategory B]
    {X Y : Over (max B)} (p : X ⟶ Y) (hp : (cartesianRelativeBoundaryCells B).rlp p)
    (hY : cartesianObjects B Y) :
    cartesianRelativeHomotopyTesting B p ↔ (monomorphisms (Over (max B))).rlp p := by
  let _ := relativeIntervalCylinder_isExact (max B)
  let _ := cartesianRelativeBoundary_isAnodyneSystem B
  let _ := over_initialMonoClass (max B)
  have hr : (cartesianRelativeBoundaryCells B).rlp.llp.rlp p := by rwa [rlp_llp_rlp]
  exact Precylinder.IsAnodyneSystem.testingEquivalences_iff_rlp_monomorphisms_of_naiveFibration
    (relativeIntervalCylinder (max B)) (cartesianRelativeBoundaryCells B).rlp.llp p hr
    ((cartesianRelativeBoundary_naiveFibrant_iff Y).mpr hY)

/-- The same reverse recognition holds for every actual dual right map with intrinsic original codomain. -/
theorem cocartesianRelativeRight_testing_iff_monoRight {B : SSet.{u}} [Quasicategory B]
    {X Y : Over (max B)} (p : X ⟶ Y) (hp : (cocartesianRelativeBoundaryCells B).rlp p)
    (hY : cocartesianObjects B Y) :
    cocartesianRelativeHomotopyTesting B p ↔ (monomorphisms (Over (max B))).rlp p := by
  let _ := relativeIntervalCylinder_isExact (max B)
  let _ := cocartesianRelativeBoundary_isAnodyneSystem B
  let _ := over_initialMonoClass (max B)
  have hr : (cocartesianRelativeBoundaryCells B).rlp.llp.rlp p := by rwa [rlp_llp_rlp]
  exact Precylinder.IsAnodyneSystem.testingEquivalences_iff_rlp_monomorphisms_of_naiveFibration
    (relativeIntervalCylinder (max B)) (cocartesianRelativeBoundaryCells B).rlp.llp p hr
    ((cocartesianRelativeBoundary_naiveFibrant_iff Y).mpr hY)

/-- Actual weak Cartesian right maps have a strict section and a whole relative marked cylinder deformation
  over their original codomain. -/
theorem cartesianRelativeRight_dualDeformation {B : SSet.{u}} [Quasicategory B]
    {X Y : Over (max B)} (p : X ⟶ Y) (hp : (cartesianRelativeBoundaryCells B).rlp p)
    (hY : cartesianObjects B Y) (hw : cartesianRelativeHomotopyTesting B p) :
    Nonempty ((relativeIntervalCylinder (max B)).DualDeformationData p) := by
  let _ := relativeIntervalCylinder_isExact (max B)
  let _ := cartesianRelativeBoundary_isAnodyneSystem B
  let _ := over_initialMonoClass (max B)
  have hr : (cartesianRelativeBoundaryCells B).rlp.llp.rlp p := by rwa [rlp_llp_rlp]
  exact Precylinder.IsAnodyneSystem.exists_dualDeformationData_of_testingEquivalence_of_naiveFibration
    (relativeIntervalCylinder (max B)) (cartesianRelativeBoundaryCells B).rlp.llp p hr
    ((cartesianRelativeBoundary_naiveFibrant_iff Y).mpr hY) hw

/-- The dual original right map has the same complete strict-section and fixed-base deformation data. -/
theorem cocartesianRelativeRight_dualDeformation {B : SSet.{u}} [Quasicategory B]
    {X Y : Over (max B)} (p : X ⟶ Y) (hp : (cocartesianRelativeBoundaryCells B).rlp p)
    (hY : cocartesianObjects B Y) (hw : cocartesianRelativeHomotopyTesting B p) :
    Nonempty ((relativeIntervalCylinder (max B)).DualDeformationData p) := by
  let _ := relativeIntervalCylinder_isExact (max B)
  let _ := cocartesianRelativeBoundary_isAnodyneSystem B
  let _ := over_initialMonoClass (max B)
  have hr : (cocartesianRelativeBoundaryCells B).rlp.llp.rlp p := by rwa [rlp_llp_rlp]
  exact Precylinder.IsAnodyneSystem.exists_dualDeformationData_of_testingEquivalence_of_naiveFibration
    (relativeIntervalCylinder (max B)) (cocartesianRelativeBoundaryCells B).rlp.llp p hr
    ((cocartesianRelativeBoundary_naiveFibrant_iff Y).mpr hY) hw

end SSet.Marked
