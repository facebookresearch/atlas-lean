/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierColimits

/-! # Small changing-object enriched coproducts, coequalizers and colimits

The genuine original Type-label and whole enriched universal properties
supply all small carrier colimits at the original scalar universe.
No fixed-label colimit is promoted without the proved label pushforward.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.CarrierColimit

/-- All small colimits exist in the actual changing-object category of original simplicial
enrichments. -/
instance hasSmallColimits : HasColimitsOfSize.{u, u} Carrier.{u} where
  has_colimits_of_shape _J _ := inferInstance

end CategoryTheory.SimplicialEnrichment.CarrierColimit
