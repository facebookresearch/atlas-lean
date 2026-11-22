/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakFilteredColimits

/-!
# Register the existing realization weak filtered-colimit theorem

The canonical full realization weak theorem supplies this instance.
The independent-universe adapter imports this registration.
-/

@[expose] public section



universe u

namespace SSet

/-- The canonical scalar theorem supplies the full filtered-colimit instance. -/
instance realizationWeakFilteredColimits :
    CategoryTheory.MorphismProperty.IsStableUnderFilteredColimits.{u, u}
      realizationWeakEquivalences.{u} :=
  realizationWeakEquivalences_stableUnderFilteredColimits

end SSet
