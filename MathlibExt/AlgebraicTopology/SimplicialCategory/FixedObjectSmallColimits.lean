/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectColimits

/-!
# Actual small coproducts, pushouts and iteration for fixed-object enrichments

The proved arbitrary presentation colimits supply all small enriched
colimits at the original scalar universe. The empty diagram retains
every original object label; coproducts and pushouts do likewise.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable {O : Type u}

/-- All small colimits exist in the genuine enriched category on the same object labels. -/
instance hasSmallColimits : HasColimitsOfSize.{u, u} (FixedObjects O) where
  has_colimits_of_shape _ _ := inferInstance

end CategoryTheory.SimplicialEnrichment.FixedObjects
