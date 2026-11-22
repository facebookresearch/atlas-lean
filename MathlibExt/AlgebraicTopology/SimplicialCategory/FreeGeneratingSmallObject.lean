/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectSmallColimits
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeGeneratorCompactness
import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# The genuine fixed-object free boundary and horn small-object arguments

The actual arbitrary enriched colimits supply pushouts, coproducts and
transfinite iteration. The proved compact original free domains supply
the required preservation of the actual relative cell-complex colimits.
Thus both literal generating families satisfy the full small-object
conditions; no enriched model structure or weak-filtration conclusion
is supplied as an input.
-/

noncomputable section
universe u
open CategoryTheory Limits
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable (O : Type u)

/-- The original free boundary family satisfies every actual small-object condition at countable length. -/
instance boundaryCardinal :
    MorphismProperty.IsCardinalForSmallObjectArgument (boundaryFamily O) Cardinal.aleph0.{u} where
  preservesColimit i hi _ _ := by
    have : IsFinitelyPresentable.{u} _ := boundaryFamily_domains_compact i hi
    infer_instance

/-- The original free horn family satisfies every actual small-object condition at countable length. -/
instance hornCardinal :
    MorphismProperty.IsCardinalForSmallObjectArgument (hornFamily O) Cardinal.aleph0.{u} where
  preservesColimit i hi _ _ := by
    have : IsFinitelyPresentable.{u} _ := hornFamily_domains_compact i hi
    infer_instance

/-- The actual free boundary maps admit the genuine small-object construction. -/
instance boundaryHasSmallObjectArgument : MorphismProperty.HasSmallObjectArgument.{u} (boundaryFamily O) where
  exists_cardinal := ⟨Cardinal.aleph0, inferInstance, inferInstance, inferInstance⟩

/-- The actual free horn maps admit the genuine small-object construction. -/
instance hornHasSmallObjectArgument : MorphismProperty.HasSmallObjectArgument.{u} (hornFamily O) where
  exists_cardinal := ⟨Cardinal.aleph0, inferInstance, inferInstance, inferInstance⟩

end CategoryTheory.SimplicialEnrichment.FixedObjects
