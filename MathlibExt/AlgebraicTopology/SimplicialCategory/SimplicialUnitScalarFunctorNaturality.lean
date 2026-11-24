/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.SimplicialUnitScalarFunctor

/-! # The SAME original whole enriched functor retains unit-to-scalar readbacks -/

noncomputable section
universe u v w
open CategoryTheory MonoidalCategory

namespace SSet
variable {C : Type v} [EnrichedCategory SSet.{u} C]
  {D : Type w} [EnrichedCategory SSet.{u} D]

/-- The SAME original full Hom map commutes literally with the actual unit-to-scalar dictionary. -/
theorem unitScalarFunctor_forget_map (F : EnrichedFunctor SSet.{u} C D) (q : SimplexCategoryᵒᵖ)
    {x y : ForgetEnrichment SSet.{u} C} (f : x ⟶ y) :
    (unitScalarFunctor D q).map (F.forget.map f) =
      (scalarFunctor F q).map ((unitScalarFunctor C q).map f) := rfl

/-- Every actual original unit-shaped source coefficient retains the SAME original enriched
Hom image in each degree. -/
theorem unitScalarFunctor_forget_hom (F : EnrichedFunctor SSet.{u} C D) (q : SimplexCategoryᵒᵖ)
    {x y : C} (f : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y)) :
    (unitScalarFunctor D q).map (F.forget.map (ForgetEnrichment.homOf SSet.{u} f)) =
      (F.map x y).app q (f.app q PUnit.unit) := rfl

end SSet
