/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentNerveBoundaryLifting
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentAdjunction
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# All original coherent-realization cofibrations

The same actual adjunction transports the genuine unrestricted full
coherent-nerve mono lifts to its original realization. Every original
simplicial mono therefore becomes an original varying-object Bergner
C0 cofibration, retaining all original object and enriched Hom maps.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization
open SimplicialEnrichment

/-- The SAME original coherent realization sends EVERY simplicial mono to the actual global Bergner C0 left class. -/
theorem realizationMap_cofibration_of_mono {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    Bergner.generatingCofibrations.rlp.llp (realizationFunctor.map i) := by
  intro C D p hp
  exact (realizationAdjunction.hasLiftingProperty_iff i p).mpr
    (OriginalNerveBoundaryLifting.bergnerRight_monoLifting p hp i)

/-- Every original boundary map, including degree zero, has its SAME original coherent realization in the global C0
class. -/
theorem boundary_realization_cofibration (n : ℕ) :
    Bergner.generatingCofibrations.rlp.llp
      (realizationFunctor.map (SSet.boundary.{u} n).ι) :=
  realizationMap_cofibration_of_mono _

end CategoryTheory.CoherentRealization
