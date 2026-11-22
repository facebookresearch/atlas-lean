/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.Core
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.PairProviders
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.RestrictionTensorData

/-!
# Tensor data for restriction of symmetric sphere modules

Packages the ordered and symmetric tensor data of a sphere module and its restriction
along the degree inclusion. The coefficient-pair formula identifies the restricted
action with the corresponding symmetric action, retaining both complete module
structures.
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

/-- The complete direct module satisfies the original ordered/symmetric coefficient-pair equation. -/
theorem directRestrictionModule_pair
    (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) (a b : N) :
    (DayFunctor.η orderedSphere.{u, v} (directRestrictionModule M).X).app (a, b) ≫
        (directRestrictionModule M).mod.smul.natTrans.app (a ⊗ b) =
      (DayFunctor.η sphereSequence.{u, v} M.X).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫
        M.mod.smul.natTrans.app (degreeInclusion.obj (a ⊗ b)) := by
  apply (Under.forget CGWH.point.{u, v}).map_injective
  have ha := congrArg
    (fun f => (Under.forget CGWH.point.{u, v}).map
      ((DayFunctor.η orderedSphere.{u, v} (U.obj M.X)).app (a, b) ≫
        f.natTrans.app (a ⊗ b)))
    (directModuleRestriction_action M)
  have hs := congrArg (Under.forget CGWH.point.{u, v}).map
    (restrictionScalarPair_action orderedSphere.{u, v} sphereSequence.{u, v} M.X M.X
      orderedSphereInclusion.{u, v} M.mod.smul a b)
  have hi :
      (orderedSphereInclusion.{u, v}.natTrans.app a ⊗ₘ 𝟙 ((U.obj M.X).functor.obj b)) =
        𝟙 ((U.obj sphereSequence.{u, v}).functor.obj a ⊗ (U.obj M.X).functor.obj b) := by
    rw [orderedSphereInclusion_app]
    exact id_tensorHom_id _ _
  have hsi := congrArg
    (fun f => (Under.forget CGWH.point.{u, v}).map
      (f ≫ (DayFunctor.η sphereSequence.{u, v} M.X).app
        (degreeInclusion.obj a, degreeInclusion.obj b) ≫
          M.mod.smul.natTrans.app (degreeInclusion.obj (a ⊗ b)))) hi
  have hid := congrArg (Under.forget CGWH.point.{u, v}).map
    (Category.id_comp ((DayFunctor.η sphereSequence.{u, v} M.X).app
      (degreeInclusion.obj a, degreeInclusion.obj b) ≫
        M.mod.smul.natTrans.app (degreeInclusion.obj (a ⊗ b))))
  exact ha.trans (hs.trans (hsi.trans hid))

/-- The whole actual native tensor, coefficient and ordinary module data precedes its pair equation. -/
def nativeRestrictionTensorData (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) :
    RestrictionTensorData.Data PointedCGWH.sphereOne.{u, v} M.X where
  ordered := inferInstance
  symmetric := originalSymmetricSequenceMonoidal.{u, v}
  orderedMonoid := orderedSphereMonObj.{u, v}
  sourceMonoid := sphereSequenceMonObj.{u, v}
  sourceModule := M.mod
  restrictedModule := (directRestrictionModule M).mod
  orderedPairing := fun F G => DayFunctor.η F G
  symmetricPairing := fun F G => DayFunctor.η F G

/-- The complete supplied source data is the same full original source module data. -/
theorem nativeRestrictionTensorData_source (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) :
    (nativeRestrictionTensorData M).sourceModule = M.mod := rfl

/-- The complete supplied restriction data retains every field of the original restricted module. -/
theorem nativeRestrictionTensorData_restricted
    (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) :
    (nativeRestrictionTensorData M).restrictedModule = (directRestrictionModule M).mod := rfl

/-- Both complete native tensors and module structures satisfy the original coefficient-pair equation. -/
theorem nativeRestrictionTensorData_formula
    (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) (a b : N) :
    (nativeRestrictionTensorData M).Formula a b := by
  apply (Under.forget CGWH.point.{u, v}).map_injective
  have ha := congrArg
    (fun f => (Under.forget CGWH.point.{u, v}).map
      ((DayFunctor.η orderedSphere.{u, v} (U.obj M.X)).app (a, b) ≫
        f.natTrans.app (a ⊗ b)))
    (directModuleRestriction_action M)
  have hs := congrArg (Under.forget CGWH.point.{u, v}).map
    (restrictionScalarPair_action orderedSphere.{u, v} sphereSequence.{u, v} M.X M.X
      orderedSphereInclusion.{u, v} M.mod.smul a b)
  have hi :
      (orderedSphereInclusion.{u, v}.natTrans.app a ⊗ₘ 𝟙 ((U.obj M.X).functor.obj b)) =
        𝟙 ((U.obj sphereSequence.{u, v}).functor.obj a ⊗ (U.obj M.X).functor.obj b) := by
    exact (congrArg (fun f => f ⊗ₘ 𝟙 ((U.obj M.X).functor.obj b))
      (orderedSphereInclusion_app a)).trans (id_tensorHom_id _ _)
  have hsi := congrArg
    (fun f => (Under.forget CGWH.point.{u, v}).map
      (f ≫ (DayFunctor.η sphereSequence.{u, v} M.X).app
        (degreeInclusion.obj a, degreeInclusion.obj b) ≫
          M.mod.smul.natTrans.app (degreeInclusion.obj (a ⊗ b)))) hi
  have hid := congrArg (Under.forget CGWH.point.{u, v}).map
    (Category.id_comp ((DayFunctor.η sphereSequence.{u, v} M.X).app
      (degreeInclusion.obj a, degreeInclusion.obj b) ≫
        M.mod.smul.natTrans.app (degreeInclusion.obj (a ⊗ b))))
  exact ha.trans (hs.trans (hsi.trans hid))

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
