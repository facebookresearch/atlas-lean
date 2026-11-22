/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.NativeRestrictionTensorData
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.RestrictionModuleObjects

/-!
# Module objects for sequential restriction

Packages a symmetric sphere module and its direct restriction as complete module objects with
coefficient, level and pairing comparisons. Proves the module-action formula at every ordered
index pair.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj


namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison
universe u v
attribute [local instance] PointedCGWH.EnrichedKan.hasSmallColimits
  originalSymmetricSequenceMonoidal originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  degreeInclusionMonoidal restrictionLaxMonoidal symmetrizationOplaxMonoidal sequenceAdjunctionIsMonoidal
  symmetrizationMonoidal orderedSphereMonObj sphereSequenceMonObj
local notation "N" => CategoryTheory.Sequence.Index

/-- The complete original pair keeps both actual module objects and every original construction field. -/
def nativeRestrictionModuleObjects (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) :
    RestrictionModuleObjects.Data (V := PointedCGWH.{u, v}) where
  ordered := inferInstance
  symmetric := originalSymmetricSequenceMonoidal.{u, v}
  orderedCoefficient := orderedSphere.{u, v}
  symmetricCoefficient := sphereSequence.{u, v}
  orderedMonoid := orderedSphereMonObj.{u, v}
  sourceMonoid := sphereSequenceMonObj.{u, v}
  source := M
  target := (directModuleRestriction.{u, v}).obj M
  coefficientIso := fun _ => Iso.refl _
  levelIso := fun _ => Iso.refl _
  orderedPairing := fun F G => DayFunctor.η F G
  symmetricPairing := fun F G => DayFunctor.η F G

/-- The source is the entire unchanged original source module. -/
theorem nativeRestrictionModuleObjects_source
    (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) :
    (nativeRestrictionModuleObjects M).source = M := rfl

/-- The target is the entire unchanged original direct restriction module. -/
theorem nativeRestrictionModuleObjects_target
    (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) :
    (nativeRestrictionModuleObjects M).target = (directModuleRestriction.{u, v}).obj M := rfl

/-- The entire original module construction proves every pair before erasing identity level maps. -/
theorem nativeRestrictionModuleObjects_formula
    (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) (a b : N) :
    (nativeRestrictionModuleObjects M).Formula a b := by
  apply (Under.forget CGWH.point.{u, v}).map_injective
  let p := (DayFunctor.η orderedSphere.{u, v} ((directModuleRestriction.{u, v}).obj M).X).app (a, b)
  let t := ((directModuleRestriction.{u, v}).obj M).mod.smul.natTrans.app (a ⊗ b)
  let q := (DayFunctor.η sphereSequence.{u, v} M.X).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫
    M.mod.smul.natTrans.app (degreeInclusion.obj (a ⊗ b))
  have hl : ((nativeRestrictionModuleObjects M).levelIso (a ⊗ b)).hom =
      𝟙 (((directModuleRestriction.{u, v}).obj M).X.functor.obj (a ⊗ b)) := rfl
  have hc :
      (tensorIso ((nativeRestrictionModuleObjects M).coefficientIso a)
        ((nativeRestrictionModuleObjects M).levelIso b)).hom =
      𝟙 (orderedSphere.{u, v}.functor.obj a ⊗
        ((directModuleRestriction.{u, v}).obj M).X.functor.obj b) :=
    id_tensorHom_id _ _
  have hlevel := congrArg
    (fun f => (Under.forget CGWH.point.{u, v}).map (p ≫ t ≫ f)) hl
  have hunit := congrArg (Under.forget CGWH.point.{u, v}).map
    (congrArg (fun f => p ≫ f) (Category.comp_id t))
  have hpair := congrArg (Under.forget CGWH.point.{u, v}).map
    (directRestrictionModule_pair M a b)
  have hcoeff := congrArg
    (fun f => (Under.forget CGWH.point.{u, v}).map (f ≫ q)) hc
  have hcoeffUnit := congrArg (Under.forget CGWH.point.{u, v}).map (Category.id_comp q)
  exact hlevel.trans (hunit.trans (hpair.trans (hcoeff.trans hcoeffUnit).symm))

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
