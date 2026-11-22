/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerIntervalGenerators
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalEquivalenceCountableIntervalDirectReadback

/-!
# Actual whole original interval point lifts from the small A2 family

Every constructed original interval is related to an actual representative
by a full fixed-label isomorphism. Its SAME point inclusion is an actual
arrow isomorphic to the original representative point. The genuine small
A2 right-lifting class therefore supplies full lifts of the SAME original
constructed intervals, retaining both original object and Hom maps.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
open FixedObjects OriginalWalkingArrowFreeSingleHomIso
variable {E D : Carrier.{u}} (r : E ⟶ D)

/-- Every SAME genuine original interval point has its actual full A2 lift via the chosen original representative
isomorphism. -/
theorem interval_point_lifting (hr : generatingIntervals.rlp r)
    (H : FixedObjects walking.{u}) (hH : intervals H) (x : walking.{u}) :
    HasLiftingProperty (pointMap H x) r := by
  obtain ⟨K, hK, ⟨e⟩⟩ := represented H hH
  let ce : K.val ≅ H.val := (Functor.Fiber.fiberInclusion).mapIso e
  have he : pointMap K x ≫ ce.hom = pointMap H x :=
    (BergnerObjects.select_comp _ ce.hom).trans (congrArg BergnerObjects.select (map_vertex e.hom x))
  let ae : Arrow.mk (pointMap K x) ≅ Arrow.mk (pointMap H x) :=
    Arrow.isoMk (Iso.refl _) ce ((Category.id_comp _).symm.trans he.symm)
  let _ : HasLiftingProperty (pointMap K x) r := hr _ (point_mem K hK x)
  exact HasLiftingProperty.of_arrow_iso_left ae r

variable (a : walking.{u} → D)
variable (e : (a (BergnerTwoObject.source (𝟙_ SSet.{u})) ⟶[SSet.{u}]
  a (BergnerTwoObject.target (𝟙_ SSet.{u}))) _⦋0⦌)
variable (he : IsIso (ComponentCategory.arrowOf D e))

/-- The SAME actual original equivalence interval point lifts against every genuine original small-A2 right map. -/
theorem original_interval_point_lifting (hr : generatingIntervals.rlp r) (x : walking.{u}) :
    HasLiftingProperty (pointMap (OriginalEquivalenceCountableInterval.fixedObject a e he) x) r :=
  interval_point_lifting r hr _ (original_interval a e he) x

end CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
