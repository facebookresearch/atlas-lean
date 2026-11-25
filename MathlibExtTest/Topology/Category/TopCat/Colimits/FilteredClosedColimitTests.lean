/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.TopCat.Colimits.FilteredClosedColimit

@[expose] public section

/-!
# Filtered closed-colimit leg consumer test

Downstream signature client for the sole public provider
`TopCat.isClosedEmbedding_ι_of_filtered_of_isClosedEmbedding`: every colimit leg of a filtered
`TopCat` diagram with closed-embedding transitions is a closed embedding.
-/

set_option autoImplicit false

open CategoryTheory Limits Topology

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.FilteredClosedColimitTests

universe u v w

section FilteredClosedLeg

theorem isClosedEmbedding_ι_client {J : Type v} [Category.{w} J] [IsFiltered J]
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (F.map f).hom)
    (j₀ : J) : IsClosedEmbedding (c.ι.app j₀).hom :=
  TopCat.isClosedEmbedding_ι_of_filtered_of_isClosedEmbedding c hc hF j₀

end FilteredClosedLeg

#check TopCat.isClosedEmbedding_ι_of_filtered_of_isClosedEmbedding
#print axioms TopCat.isClosedEmbedding_ι_of_filtered_of_isClosedEmbedding

end MathlibExtTest.AlgebraicTopology.ModelCategory.FilteredClosedColimitTests
