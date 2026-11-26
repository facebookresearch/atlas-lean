/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectColimits

/-!
# Small colimits of fixed-object simplicial enrichments

Presentation colimits give small colimits in the category of enrichments
on a fixed object set. The initial enrichment, coproducts and pushouts
all retain that object set.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable {O : Type u}

/-- All small colimits exist in the enriched category on the same object labels. -/
instance hasSmallColimits : HasColimitsOfSize.{u, u} (FixedObjects O) where
  has_colimits_of_shape _ _ := inferInstance

end CategoryTheory.SimplicialEnrichment.FixedObjects
