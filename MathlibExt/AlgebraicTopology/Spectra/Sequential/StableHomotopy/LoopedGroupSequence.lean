/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.LoopedLevelSequences
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.GroupFunctors
import MathlibExt.Algebra.Category.Grp.FilteredColimitExactness

/-!
# Exact group colimits of the original looped Serre sequences

At a fixed original level and fixed positive homotopy degree, all actual
loop iterates form the original natural Serre sequence diagram. Its three
group functors and original connecting natural transformation give actual
group diagrams and maps. The same chosen filtered group quotient maps
preserve each of the three exact pairs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedGroupSequence

open PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedLevelSequences
open SSet.FibrationSequence.Geometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y)
  (hp : ∀ r : ℕ, fibrations PointedCGWH.{u, v} (levelMap p r)) (m : ℕ)

/-- Every original looped total-space group is kept in the actual sequence diagram. -/
def loopedTotalGroupDiagram (k : ℕ) : ℕ ⥤ GrpCat.{v} :=
  loopedSequenceDiagram p hp m ⋙ totalGroupFunctor k

/-- Every original looped base-space group is kept in that same actual sequence diagram. -/
def loopedBaseGroupDiagram (k : ℕ) : ℕ ⥤ GrpCat.{v} :=
  loopedSequenceDiagram p hp m ⋙ baseGroupFunctor k

/-- Every original looped sequence fiber group is kept in the same original diagram. -/
def loopedFiberGroupDiagram (k : ℕ) : ℕ ⥤ GrpCat.{v} :=
  loopedSequenceDiagram p hp m ⋙ fiberGroupFunctor k

/-- The complete group projection uses the unchanged original Serre projections. -/
def loopedProjectionGroupMap (k : ℕ) :
    loopedTotalGroupDiagram p hp m k ⟶ loopedBaseGroupDiagram p hp m k :=
  Functor.whiskerLeft (loopedSequenceDiagram p hp m) (projectionGroupNatTrans k)

/-- The complete group inclusion uses every unchanged original Serre fiber inclusion. -/
def loopedInclusionGroupMap (k : ℕ) :
    loopedFiberGroupDiagram p hp m k ⟶ loopedTotalGroupDiagram p hp m k :=
  Functor.whiskerLeft (loopedSequenceDiagram p hp m) (inclusionGroupNatTrans k)

/-- The strictly natural original connecting map is taken at the fixed homotopy degree. -/
def loopedConnectingGroupMap (k : ℕ) :
    loopedBaseGroupDiagram p hp m (k + 1) ⟶ loopedFiberGroupDiagram p hp m k :=
  Functor.whiskerLeft (loopedSequenceDiagram p hp m) (connectingGroupNatTrans k)

/-- Every original looped stage is exact at its actual total-space group. -/
theorem loopedStage_exact_at_total (k n : ℕ) :
    Function.MulExact ((loopedInclusionGroupMap p hp m k).app n).hom
      ((loopedProjectionGroupMap p hp m k).app n).hom :=
  groupExact_at_total k (iterationLevelSerreSequence p hp n m)

/-- Every original looped stage is exact at its actual fiber group. -/
theorem loopedStage_exact_at_fiber (k n : ℕ) :
    Function.MulExact ((loopedConnectingGroupMap p hp m k).app n).hom
      ((loopedInclusionGroupMap p hp m k).app n).hom :=
  groupExact_at_fiber k (iterationLevelSerreSequence p hp n m)

/-- Every original looped stage is exact at the actual next-degree base group. -/
theorem loopedStage_exact_at_base (k n : ℕ) :
    Function.MulExact ((loopedProjectionGroupMap p hp m (k + 1)).app n).hom
      ((loopedConnectingGroupMap p hp m k).app n).hom :=
  groupExact_at_base k (iterationLevelSerreSequence p hp n m)

/-- The same original chosen quotient maps are exact at the looped total colimit. -/
theorem loopedColimit_exact_at_total (k : ℕ) :
    Function.MulExact
      (GrpCat.FilteredColimits.colimitMap (loopedInclusionGroupMap p hp m k)).hom
      (GrpCat.FilteredColimits.colimitMap (loopedProjectionGroupMap p hp m k)).hom :=
  GrpCat.FilteredColimits.colimitMap_mulExact _ _ (loopedStage_exact_at_total p hp m k)

/-- The actual connecting quotient map is exact at the original looped fiber colimit. -/
theorem loopedColimit_exact_at_fiber (k : ℕ) :
    Function.MulExact
      (GrpCat.FilteredColimits.colimitMap (loopedConnectingGroupMap p hp m k)).hom
      (GrpCat.FilteredColimits.colimitMap (loopedInclusionGroupMap p hp m k)).hom :=
  GrpCat.FilteredColimits.colimitMap_mulExact _ _ (loopedStage_exact_at_fiber p hp m k)

/-- The actual connecting quotient map is exact at the original next-degree base colimit. -/
theorem loopedColimit_exact_at_base (k : ℕ) :
    Function.MulExact
      (GrpCat.FilteredColimits.colimitMap (loopedProjectionGroupMap p hp m (k + 1))).hom
      (GrpCat.FilteredColimits.colimitMap (loopedConnectingGroupMap p hp m k)).hom :=
  GrpCat.FilteredColimits.colimitMap_mulExact _ _ (loopedStage_exact_at_base p hp m k)

end PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedGroupSequence
