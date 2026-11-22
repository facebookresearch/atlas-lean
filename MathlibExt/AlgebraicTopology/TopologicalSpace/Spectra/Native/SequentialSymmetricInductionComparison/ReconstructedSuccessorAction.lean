/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.RestrictionOperators

/-!
# Successor actions of reconstructed symmetric modules

Restricting the reconstructed symmetric sphere module along the degree inclusion gives the
specified sequential successor structure map. The comparison uses the degree-one successor
arrow, the degree tensor isomorphism and the unit map on the sphere coefficient.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open CategoryTheory.Spectra.SpectrumIndexMaps
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison
universe u v
attribute [local instance] PointedCGWH.EnrichedKan.hasSmallColimits
  originalSymmetricSequenceMonoidal originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  degreeInclusionMonoidal restrictionLaxMonoidal symmetrizationOplaxMonoidal sequenceAdjunctionIsMonoidal
  orderedSphereMonObj sphereSequenceMonObj
local notation "N" => CategoryTheory.Sequence.Index

/-- The original one-step ordered arrow retains its complete forward degree transport. -/
def degreeSuccessorArrow (n : ℕ) :
    CategoryTheory.Sequence.index 1 ⊗ CategoryTheory.Sequence.index n ⟶
      CategoryTheory.Sequence.index (n + 1) :=
  eqToHom ((CategoryTheory.Sequence.tensorObj_index 1 n).trans
    (congrArg CategoryTheory.Sequence.index (Nat.one_add n)))

/-- The full reconstructed symmetric action on the original successor arrow has the original source structure map. -/
theorem reconstructedModule_successor_original
    (F : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) (n : ℕ) :
    ((λ_ PointedCGWH.sphereOne.{u, v}).inv ⊗ₘ
      𝟙 ((PointedCGWH.SymmetricModulePresentation.reconstructedModule F).X.functor.obj
        (degreeInclusion.obj (CategoryTheory.Sequence.index n)))) ≫
      PointedCGWH.SymmetricModulePresentation.arrowAction
        (PointedCGWH.SymmetricModulePresentation.reconstructedModule F)
        (degreeInclusion.obj (CategoryTheory.Sequence.index 1))
        (degreeInclusion.obj (CategoryTheory.Sequence.index n))
        (degreeInclusion.obj (CategoryTheory.Sequence.index (n + 1)))
        ((degreeTensorIso (CategoryTheory.Sequence.index 1) (CategoryTheory.Sequence.index n)).hom ≫
          degreeInclusion.map (degreeSuccessorArrow n)) =
      symmetricToSequentialSourceStructureMap.{u, v} F n := by
  let a := CategoryTheory.Sequence.index 1
  let b := CategoryTheory.Sequence.index n
  let c := CategoryTheory.Sequence.index (n + 1)
  let f : a ⊗ b ⟶ c := degreeSuccessorArrow n
  let X := F.toEnrichedFunctor.obj
    (PointedCGWH.symmetricOperatorObj.{u, v} (card n))
  let Y := F.toEnrichedFunctor.obj
    (PointedCGWH.symmetricOperatorObj.{u, v} (card (n + 1)))
  let A := TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} 1
  let l : PointedCGWH.sphereOne.{u, v} ⊗ X ⟶ A ⊗ X :=
    (λ_ PointedCGWH.sphereOne.{u, v}).inv ⊗ₘ 𝟙 X
  let H := PointedCGWH.symmetricOperatorObj.{u, v} (card n) ⟶[PointedCGWH.{u, v}]
    PointedCGWH.symmetricOperatorObj.{u, v} (card (n + 1))
  let q : H ⟶ (ihom X).obj Y := F.toEnrichedFunctor.map
    (PointedCGWH.symmetricOperatorObj.{u, v} (card n))
    (PointedCGWH.symmetricOperatorObj.{u, v} (card (n + 1)))
  have hm := reconstructedModule_arrowAction_closed F
    (degreeInclusion.obj a) (degreeInclusion.obj b) (degreeInclusion.obj c)
    ((degreeTensorIso a b).hom ≫ degreeInclusion.map f)
  have hg := degreeInclusion_operatorGenerator.{u, v} 1 n (n + 1) (Nat.add_comm 1 n) f
  exact (congrArg (fun t : A ⊗ X ⟶ Y => l ≫ t) hm).trans
    (congrArg (fun g : A ⟶ H =>
      l ≫ (β_ X A).inv ≫ (X ◁ g) ≫ MonoidalClosed.uncurry q) hg)

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
