/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierColimits

/-!
# Small colimits of simplicial enrichments

Small colimits are obtained by taking the colimit of object sets and then
a fixed-object enriched colimit over those labels. This gives coproducts,
coequalizers and colimits of arbitrary small diagrams.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.CarrierColimit

/-- All small colimits exist in the changing-object category of simplicial
enrichments. -/
instance hasSmallColimits : HasColimitsOfSize.{u, u} Carrier.{u} where
  has_colimits_of_shape _J _ := inferInstance

end CategoryTheory.SimplicialEnrichment.CarrierColimit
