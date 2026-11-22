/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.LiteralProviderPair
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.LanComparison

/-!
# Day pair actions under sequential restriction

Computes the symmetric sphere-module pair action after restriction along the degree inclusion.
Every ordered pair retains the complete Day-convolution pairing and module action, with identity
level and coefficient comparisons made explicit.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison
attribute [local instance] PointedCGWH.EnrichedKan.hasSmallColimits
  originalSymmetricSequenceMonoidal originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  degreeInclusionMonoidal restrictionLaxMonoidal symmetrizationOplaxMonoidal sequenceAdjunctionIsMonoidal
  symmetrizationMonoidal orderedSphereMonObj sphereSequenceMonObj
local notation "N" => CategoryTheory.Sequence.Index
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

/-- Every original public symmetric pair is exactly its full original Day action value. -/
theorem symmetricPairAction_value (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) (a b : I) :
    PointedCGWH.SymmetricModulePresentation.pairAction M a b =
      (DayFunctor.η sphereSequence.{u, v} M.X).app (a, b) ≫ M.mod.smul.natTrans.app (a ⊗ b) := rfl

/-- The original restricted module keeps the full explicit symmetric Day pair on every ordered degree. -/
theorem directModuleRestriction_pair_action
    (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) (a b : N) :
    (DayFunctor.η orderedSphere.{u, v} ((directModuleRestriction.{u, v}).obj M).X).app (a, b) ≫
      ((directModuleRestriction.{u, v}).obj M).mod.smul.natTrans.app (a ⊗ b) =
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

/-- Direct restriction retains every full ordered pair action of the original symmetric sphere module. -/
theorem directModuleRestriction_pair (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) (a b : N) :
    (DayFunctor.η orderedSphere.{u, v} ((directModuleRestriction.{u, v}).obj M).X).app (a, b) ≫
      ((directModuleRestriction.{u, v}).obj M).mod.smul.natTrans.app (a ⊗ b) =
    PointedCGWH.SymmetricModulePresentation.pairAction M (degreeInclusion.obj a) (degreeInclusion.obj b) :=
  (directModuleRestriction_pair_action M a b).trans
    (symmetricPairAction_value M (degreeInclusion.obj a) (degreeInclusion.obj b)).symm

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
