/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeFibrantCodomainRecognition
import MathlibExt.AlgebraicTopology.ModelCategory.AnodyneTesting
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingTwoOutOfThree

/-!
# The original accessible replacements retain relative homotopy testing

The unchanged original fixed-base replacement unit lies in the proved
small relative anodyne class. Its whole natural unit square and native
two-out-of-three therefore preserve and reflect all original intrinsic
target homotopy testing. Both endpoints of every original arrow are
replaced; no accessibility of the full mapping weak class is inferred
from replacement accessibility alone.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace SSet.Marked

/-- The original Cartesian replacement unit is in the actual relative small anodyne left class. -/
theorem cartesianFixedBaseReplacementUnit_relativeAnodyne (B : SSet.{u}) (X : Over (max B)) :
    (cartesianRelativeBoundaryCells B).rlp.llp ((cartesianFixedBaseReplacementUnit B).app X) :=
  antitone_llp (antitone_rlp (cartesianFixedBaseCells_le_relativeBoundary B)) _
    (cartesianFixedBaseReplacementUnit_left B X)

/-- The unchanged original dual replacement unit belongs to the genuine dual relative anodyne class. -/
theorem cocartesianFixedBaseReplacementUnit_relativeAnodyne (B : SSet.{u}) (X : Over (max B)) :
    (cocartesianRelativeBoundaryCells B).rlp.llp ((cocartesianFixedBaseReplacementUnit B).app X) :=
  antitone_llp (antitone_rlp (cocartesianFixedBaseCells_le_relativeBoundary B)) _
    (cocartesianFixedBaseReplacementUnit_left B X)

/-- The original Cartesian unit is weak for all actual intrinsic relative homotopy tests. -/
theorem cartesianFixedBaseReplacementUnit_relativeTesting (B : SSet.{u}) [Quasicategory B]
    (X : Over (max B)) :
    cartesianRelativeHomotopyTesting B ((cartesianFixedBaseReplacementUnit B).app X) := by
  let _ := relativeIntervalCylinder_isExact (max B)
  let _ := cartesianRelativeBoundary_isAnodyneSystem B
  exact Precylinder.IsAnodyneSystem.anodyne_le_testingEquivalences
    (relativeIntervalCylinder (max B)) (cartesianRelativeBoundaryCells B).rlp.llp _
    (cartesianFixedBaseReplacementUnit_relativeAnodyne B X)

/-- Every original dual unit has the same actual all-target homotopy weakness. -/
theorem cocartesianFixedBaseReplacementUnit_relativeTesting (B : SSet.{u}) [Quasicategory B]
    (X : Over (max B)) :
    cocartesianRelativeHomotopyTesting B ((cocartesianFixedBaseReplacementUnit B).app X) := by
  let _ := relativeIntervalCylinder_isExact (max B)
  let _ := cocartesianRelativeBoundary_isAnodyneSystem B
  exact Precylinder.IsAnodyneSystem.anodyne_le_testingEquivalences
    (relativeIntervalCylinder (max B)) (cocartesianRelativeBoundaryCells B).rlp.llp _
    (cocartesianFixedBaseReplacementUnit_relativeAnodyne B X)

/-- The same original Cartesian replacement preserves and reflects the full relative homotopy testing of
  every original arrow. -/
theorem cartesianFixedBaseReplacement_map_relativeTesting_iff {B : SSet.{u}} [Quasicategory B]
    {X Y : Over (max B)} (f : X ⟶ Y) :
    cartesianRelativeHomotopyTesting B ((cartesianFixedBaseReplacementFunctor B).map f) ↔
      cartesianRelativeHomotopyTesting B f := by
  let W := cartesianRelativeHomotopyTesting B
  let _ : W.HasTwoOutOfThreeProperty := Precylinder.testingEquivalences.hasTwoOutOfThreeProperty _ _
  let η := cartesianFixedBaseReplacementUnit B
  let R := cartesianFixedBaseReplacementFunctor B
  have hX : W (η.app X) := cartesianFixedBaseReplacementUnit_relativeTesting B X
  have hY : W (η.app Y) := cartesianFixedBaseReplacementUnit_relativeTesting B Y
  have heq : η.app X ≫ R.map f = f ≫ η.app Y := (η.naturality f).symm
  have hbridge : W (η.app X ≫ R.map f) ↔ W (f ≫ η.app Y) :=
    (congrArg (fun g : X ⟶ R.obj Y => W g) heq).to_iff
  exact (W.precomp_iff (W' := W) (η.app X) (R.map f) hX).symm.trans
    (hbridge.trans (W.postcomp_iff (W' := W) f (η.app Y) hY))

/-- The dual original unit square detects all original relative homotopy testing in exactly the same way. -/
theorem cocartesianFixedBaseReplacement_map_relativeTesting_iff {B : SSet.{u}} [Quasicategory B]
    {X Y : Over (max B)} (f : X ⟶ Y) :
    cocartesianRelativeHomotopyTesting B ((cocartesianFixedBaseReplacementFunctor B).map f) ↔
      cocartesianRelativeHomotopyTesting B f := by
  let W := cocartesianRelativeHomotopyTesting B
  let _ : W.HasTwoOutOfThreeProperty := Precylinder.testingEquivalences.hasTwoOutOfThreeProperty _ _
  let η := cocartesianFixedBaseReplacementUnit B
  let R := cocartesianFixedBaseReplacementFunctor B
  have hX : W (η.app X) := cocartesianFixedBaseReplacementUnit_relativeTesting B X
  have hY : W (η.app Y) := cocartesianFixedBaseReplacementUnit_relativeTesting B Y
  have heq : η.app X ≫ R.map f = f ≫ η.app Y := (η.naturality f).symm
  have hbridge : W (η.app X ≫ R.map f) ↔ W (f ≫ η.app Y) :=
    (congrArg (fun g : X ⟶ R.obj Y => W g) heq).to_iff
  exact (W.precomp_iff (W' := W) (η.app X) (R.map f) hX).symm.trans
    (hbridge.trans (W.postcomp_iff (W' := W) f (η.app Y) hY))

end SSet.Marked
