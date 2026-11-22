/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeReplacementTesting
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeBoundaryFactorAccessibility
import MathlibExt.CategoryTheory.MorphismProperty.LiftingTest

/-!
# A genuine small lifting test for all original relative homotopy weak arrows

Replace both original endpoints by the unchanged intrinsic replacement,
then factor that literal arrow by the proved completed small anodyne
family. Its right factor has its original intrinsic codomain. Actual
fibrant-codomain reverse recognition tests its weakness by the original
small mono generators. Thus the native tagged lifting test detects every
original arrow, not merely arrows of bounded size or a terminal test.
The comparison with the full mapping weak class remains to be proved.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace SSet.Marked

/-- The actual original replaced Cartesian Arrow is followed by the genuine completed right-factor Arrow functor. -/
def cartesianRelativeTestRightFactor (B : SSet.{u}) : Arrow (Over (max B)) ⥤ Arrow (Over (max B)) :=
  (cartesianFixedBaseReplacementFunctor B).mapArrow ⋙
    (RelativeBoundarySmallObject.cartesianFunctorialFactorization B).originalRightFactorFunctor

/-- The original dual endpoint replacements and completed factors give the same literal dual testing functor. -/
def cocartesianRelativeTestRightFactor (B : SSet.{u}) : Arrow (Over (max B)) ⥤ Arrow (Over (max B)) :=
  (cocartesianFixedBaseReplacementFunctor B).mapArrow ⋙
    (RelativeBoundarySmallObject.cocartesianFunctorialFactorization B).originalRightFactorFunctor

/-- Every actual Cartesian test right factor retains its original completed ordinal and replaced whole input arrow. -/
theorem cartesianRelativeTestRightFactor_obj (B : SSet.{u}) (f : Arrow (Over (max B))) :
    (cartesianRelativeTestRightFactor B).obj f =
      Arrow.mk ((RelativeBoundarySmallObject.cartesianFunctorialFactorization B).p.app
        ((cartesianFixedBaseReplacementFunctor B).mapArrow.obj f)) := rfl

/-- The dual original test Arrow has the same full native right-factor formula. -/
theorem cocartesianRelativeTestRightFactor_obj (B : SSet.{u}) (f : Arrow (Over (max B))) :
    (cocartesianRelativeTestRightFactor B).obj f =
      Arrow.mk ((RelativeBoundarySmallObject.cocartesianFunctorialFactorization B).p.app
        ((cocartesianFixedBaseReplacementFunctor B).mapArrow.obj f)) := rfl

/-- The actual small tagged mono lifting functor follows the two original Cartesian source functors. -/
def cartesianRelativeWeakLiftingTest (B : SSet.{u}) : Arrow (Over (max B)) ⥤ Arrow (Type u) := by
  let _ : Small.{u} (FixedBaseMonoIndex B) := fixedBaseMonoIndex_small B
  exact cartesianRelativeTestRightFactor B ⋙ LiftingTest.smallFunctor.{u} (fixedBaseMonoCell B)

/-- The same whole dual test retains every original mono tag and native square. -/
def cocartesianRelativeWeakLiftingTest (B : SSet.{u}) : Arrow (Over (max B)) ⥤ Arrow (Type u) := by
  let _ : Small.{u} (FixedBaseMonoIndex B) := fixedBaseMonoIndex_small B
  exact cocartesianRelativeTestRightFactor B ⋙ LiftingTest.smallFunctor.{u} (fixedBaseMonoCell B)

/-- The actual completed Cartesian right factor is weak exactly when its whole original replaced input is
  homotopy testing weak. -/
theorem cartesianRelativeTestRightFactor_testing_iff (B : SSet.{u}) [Quasicategory B]
    (f : Arrow (Over (max B))) :
    cartesianRelativeHomotopyTesting B ((cartesianRelativeTestRightFactor B).obj f).hom ↔
      cartesianRelativeHomotopyTesting B f.hom := by
  let W := cartesianRelativeHomotopyTesting B
  let _ : W.HasTwoOutOfThreeProperty := Precylinder.testingEquivalences.hasTwoOutOfThreeProperty _ _
  let d := RelativeBoundarySmallObject.cartesianFunctorialFactorization B
  let g := (cartesianFixedBaseReplacementFunctor B).mapArrow.obj f
  let _ := relativeIntervalCylinder_isExact (max B)
  let _ := cartesianRelativeBoundary_isAnodyneSystem B
  have hi : W (d.i.app g) := Precylinder.IsAnodyneSystem.anodyne_le_testingEquivalences
    (relativeIntervalCylinder (max B)) (cartesianRelativeBoundaryCells B).rlp.llp _ (d.hi g)
  have hg : W (d.i.app g ≫ d.p.app g) ↔ W g.hom := (congrArg (fun a => W a) (show d.i.app g ≫ d.p.app g =
    g.hom from d.fac_app)).to_iff
  exact (W.precomp_iff (W' := W) (d.i.app g) (d.p.app g) hi).symm.trans
    (hg.trans (cartesianFixedBaseReplacement_map_relativeTesting_iff f.hom))

/-- The original dual input and its actual test factor have exactly the same all-target homotopy weakness. -/
theorem cocartesianRelativeTestRightFactor_testing_iff (B : SSet.{u}) [Quasicategory B]
    (f : Arrow (Over (max B))) :
    cocartesianRelativeHomotopyTesting B ((cocartesianRelativeTestRightFactor B).obj f).hom ↔
      cocartesianRelativeHomotopyTesting B f.hom := by
  let W := cocartesianRelativeHomotopyTesting B
  let _ : W.HasTwoOutOfThreeProperty := Precylinder.testingEquivalences.hasTwoOutOfThreeProperty _ _
  let d := RelativeBoundarySmallObject.cocartesianFunctorialFactorization B
  let g := (cocartesianFixedBaseReplacementFunctor B).mapArrow.obj f
  let _ := relativeIntervalCylinder_isExact (max B)
  let _ := cocartesianRelativeBoundary_isAnodyneSystem B
  have hi : W (d.i.app g) := Precylinder.IsAnodyneSystem.anodyne_le_testingEquivalences
    (relativeIntervalCylinder (max B)) (cocartesianRelativeBoundaryCells B).rlp.llp _ (d.hi g)
  have hg : W (d.i.app g ≫ d.p.app g) ↔ W g.hom := (congrArg (fun a => W a) (show d.i.app g ≫ d.p.app g =
    g.hom from d.fac_app)).to_iff
  exact (W.precomp_iff (W' := W) (d.i.app g) (d.p.app g) hi).symm.trans
    (hg.trans (cocartesianFixedBaseReplacement_map_relativeTesting_iff f.hom))

/-- Surjectivity of the genuine same-map small Cartesian test is exactly all-target relative homotopy
  weakness of every original arrow. -/
theorem cartesianRelativeWeakLiftingTest_surjective_iff (B : SSet.{u}) [Quasicategory B]
    (f : Arrow (Over (max B))) :
    Function.Surjective ((cartesianRelativeWeakLiftingTest B).obj f).hom ↔
      cartesianRelativeHomotopyTesting B f.hom := by
  let _ : Small.{u} (FixedBaseMonoIndex B) := fixedBaseMonoIndex_small B
  let d := RelativeBoundarySmallObject.cartesianFunctorialFactorization B
  let g := (cartesianFixedBaseReplacementFunctor B).mapArrow.obj f
  let p := d.p.app g
  have hY : cartesianObjects B g.right := cartesianFixedBaseReplacement_intrinsic f.right
  change Function.Surjective ((LiftingTest.smallFunctor.{u} (fixedBaseMonoCell B)).obj (Arrow.mk p)).hom ↔ _
  rw [LiftingTest.smallFunctor_surjective_iff]
  have hI : (ofHoms (fun s => (fixedBaseMonoCell B s).hom)).rlp p ↔ (monomorphisms (Over (max B))).rlp p :=
    fixedBaseMonoCells_rlp_iff p
  exact hI.trans ((cartesianRelativeRight_testing_iff_monoRight p (d.hp g) hY).symm.trans
    (cartesianRelativeTestRightFactor_testing_iff B f))

/-- The dual genuine tagged test likewise detects every original arrow with its complete original marks and
  base maps. -/
theorem cocartesianRelativeWeakLiftingTest_surjective_iff (B : SSet.{u}) [Quasicategory B]
    (f : Arrow (Over (max B))) :
    Function.Surjective ((cocartesianRelativeWeakLiftingTest B).obj f).hom ↔
      cocartesianRelativeHomotopyTesting B f.hom := by
  let _ : Small.{u} (FixedBaseMonoIndex B) := fixedBaseMonoIndex_small B
  let d := RelativeBoundarySmallObject.cocartesianFunctorialFactorization B
  let g := (cocartesianFixedBaseReplacementFunctor B).mapArrow.obj f
  let p := d.p.app g
  have hY : cocartesianObjects B g.right := cocartesianFixedBaseReplacement_intrinsic f.right
  change Function.Surjective ((LiftingTest.smallFunctor.{u} (fixedBaseMonoCell B)).obj (Arrow.mk p)).hom ↔ _
  rw [LiftingTest.smallFunctor_surjective_iff]
  have hI : (ofHoms (fun s => (fixedBaseMonoCell B s).hom)).rlp p ↔ (monomorphisms (Over (max B))).rlp p :=
    fixedBaseMonoCells_rlp_iff p
  exact hI.trans ((cocartesianRelativeRight_testing_iff_monoRight p (d.hp g) hY).symm.trans
    (cocartesianRelativeTestRightFactor_testing_iff B f))

end SSet.Marked
