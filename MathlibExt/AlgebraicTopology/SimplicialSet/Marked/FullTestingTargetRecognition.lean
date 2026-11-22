/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FixedBaseReplacementWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverCotensorBoundaryZero

/-!
# Full weak-mono terminal testing recognizes the original intrinsic targets

The actual scalar degree-zero cotensor boundary is the original terminal
arrow. Full weak marked monos therefore lift into every actual intrinsic
target. Conversely the original fixed-base family is now proved to consist
of full weak marked monos, so these terminal tests imply the original
intrinsic fibration and exact markings. This is terminal-object recognition,
not a uniform small test family or a full marked-model recognition theorem.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty

namespace SSet.Marked

/-- Every original intrinsic Cartesian target lifts all full weak marked monomorphisms, through the same
  native zero-boundary comparison. -/
theorem cartesianTesting_terminal_of_intrinsic {B : SSet.{u}} [Quasicategory B]
    (Y : Over (max B)) (hY : cartesianObjects B Y) :
    cartesianTestingFibrations B (Over.mkIdTerminal.from Y) := by
  let target : CartesianOver B := ⟨Y, hY⟩
  intro X X' i hi
  have h := ((cartesianTestingTrivialCofibrations_iff_cotensor i).mp hi).2
  have hp : HasLiftingProperty i (overCotensorBoundary (max B) Y 0) :=
    h _ (by
      simp only [cartesianCotensorBoundaryTests, iSup_iff]
      exact ⟨target, ofHoms.mk 0⟩)
  exact (HasLiftingProperty.iff_of_arrow_iso_right i (overCotensorBoundaryZeroArrowIso (max B) Y)).mp hp

/-- Every original intrinsic cocartesian target obeys the same complete full weak-mono terminal lifting property. -/
theorem cocartesianTesting_terminal_of_intrinsic {B : SSet.{u}} [Quasicategory B]
    (Y : Over (max B)) (hY : cocartesianObjects B Y) :
    cocartesianTestingFibrations B (Over.mkIdTerminal.from Y) := by
  let target : CocartesianOver B := ⟨Y, hY⟩
  intro X X' i hi
  have h := ((cocartesianTestingTrivialCofibrations_iff_cotensor i).mp hi).2
  have hp : HasLiftingProperty i (overCotensorBoundary (max B) Y 0) :=
    h _ (by
      simp only [cocartesianCotensorBoundaryTests, iSup_iff]
      exact ⟨target, ofHoms.mk 0⟩)
  exact (HasLiftingProperty.iff_of_arrow_iso_right i (overCotensorBoundaryZeroArrowIso (max B) Y)).mp hp

/-- The terminal right class of all original Cartesian weak marked monos is exactly the original intrinsic
  target class. -/
theorem cartesianTesting_terminal_iff_intrinsic {B : SSet.{u}} [Quasicategory B] (Y : Over (max B)) :
    cartesianTestingFibrations B (Over.mkIdTerminal.from Y) ↔ cartesianObjects B Y := by
  constructor
  · intro h
    apply (cartesianFixedBaseCells_terminal_rlp_iff Y).mp
    exact antitone_rlp (cartesianFixedBaseCells_le_testing B) _ h
  · exact cartesianTesting_terminal_of_intrinsic Y

/-- The full dual weak-mono terminal tests recognize precisely the same original cocartesian projection and mark set. -/
theorem cocartesianTesting_terminal_iff_intrinsic {B : SSet.{u}} [Quasicategory B] (Y : Over (max B)) :
    cocartesianTestingFibrations B (Over.mkIdTerminal.from Y) ↔ cocartesianObjects B Y := by
  constructor
  · intro h
    apply (cocartesianFixedBaseCells_terminal_rlp_iff Y).mp
    exact antitone_rlp (cocartesianFixedBaseCells_le_testing B) _ h
  · exact cocartesianTesting_terminal_of_intrinsic Y

/-- The same actual original Cartesian replacement targets pass the full weak-mono terminal tests. -/
theorem cartesianFixedBaseReplacement_full_testing {B : SSet.{u}} [Quasicategory B]
    (X : Over (max B)) : cartesianTestingFibrations B
      (Over.mkIdTerminal.from ((cartesianFixedBaseReplacementFunctor B).obj X)) :=
  cartesianTesting_terminal_of_intrinsic _ (cartesianFixedBaseReplacement_intrinsic X)

/-- The unchanged dual replacement retains full intrinsic terminal testing on its actual original target. -/
theorem cocartesianFixedBaseReplacement_full_testing {B : SSet.{u}} [Quasicategory B]
    (X : Over (max B)) : cocartesianTestingFibrations B
      (Over.mkIdTerminal.from ((cocartesianFixedBaseReplacementFunctor B).obj X)) :=
  cocartesianTesting_terminal_of_intrinsic _ (cocartesianFixedBaseReplacement_intrinsic X)

end SSet.Marked
