/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjective

/-!
# Coefficient maps of the enriched projective generators

The full original enriched generator family is the family of literal
coefficient maps of the free enriched functors.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.MorphismProperty CategoryTheory.MonoidalCategory

namespace HomotopicalAlgebra.EnrichedProjective

universe uV vV uI
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] {I : Type uI} [EnrichedCategory V I]

/-- The complete original enriched generator definition uses its literal coefficient maps. -/
theorem generators_eq_coefficient_ofHoms (P : MorphismProperty V) :
    HomotopicalAlgebra.EnrichedProjective.generators (A := I) P =
      MorphismProperty.ofHoms (fun q : I × P.toSet =>
        CategoryTheory.EnrichedFunctorCat.Free.coefficientMap q.1 q.2.1.hom) := rfl

end HomotopicalAlgebra.EnrichedProjective
