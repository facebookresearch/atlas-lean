/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.Core
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.RestrictionSpectrumStructures

/-!
# Structure maps of restricted symmetric spectra

Restricting a sphere module along the degree inclusion gives a sequential
spectrum. Its structure map is expressed as the degree-one coefficient
comparison followed by the Day convolution insertion, module action, and
transport from the tensor-product index to the successor degree.
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

/-- The complete native restriction keeps the original left structure map, action and forward degree arrow. -/
theorem directModuleRestriction_structureMap_original
    (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) (n : ℕ) :
    CategoryTheory.Sequence.TensorPowerModule.structureMap
      ((directModuleRestriction.{u, v}).obj M) n =
      ((λ_ PointedCGWH.sphereOne.{u, v}).inv ⊗ₘ
        𝟙 (((directModuleRestriction.{u, v}).obj M).X.functor.obj
          (CategoryTheory.Sequence.index n))) ≫
      (DayFunctor.η sphereSequence.{u, v} M.X).app
        (degreeInclusion.obj (CategoryTheory.Sequence.index 1),
         degreeInclusion.obj (CategoryTheory.Sequence.index n)) ≫
      M.mod.smul.natTrans.app (degreeInclusion.obj
        (CategoryTheory.Sequence.index 1 ⊗ CategoryTheory.Sequence.index n)) ≫
      M.X.functor.map (degreeInclusion.map
        (eqToHom ((CategoryTheory.Sequence.tensorObj_index 1 n).trans
          (congrArg CategoryTheory.Sequence.index (Nat.one_add n))))) := by
  apply (Under.forget CGWH.point.{u, v}).map_injective
  exact congrArg (Under.forget CGWH.point.{u, v}).map
    (CoefficientRestriction.moduleData_structureMap_original PointedCGWH.sphereOne.{u, v}
      M.X M.mod.smul (directRestrictionModule_one M) (directRestrictionModule_mul M) n)

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
