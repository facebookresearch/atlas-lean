/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentRealizationCofibrations
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerCofibrationHomMonicity

/-!
# Every SAME original simplicial mono is monic on full coherent Homs

The actual original coherent realization sends every mono to the proved
Bergner C0 class. The existing full original Hom-monicity theorem then
applies to the SAME original enriched map and both original vertices.
No target fibrancy or global Quillen-equivalence outcome is assumed.
-/

noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization

/-- Every original simplicial mono is monic on the SAME complete original realized Hom map. -/
theorem realizationMap_full_hom_mono {K L : SSet.{u}} (f : K ⟶ L) [Mono f] (x y : K _⦋0⦌) :
    Mono ((realizationMap f).map x y) :=
  SimplicialEnrichment.Bergner.cofibration_original_hom_mono (realizationFunctor.map f)
    (realizationMap_cofibration_of_mono f) x y

end CategoryTheory.CoherentRealization
