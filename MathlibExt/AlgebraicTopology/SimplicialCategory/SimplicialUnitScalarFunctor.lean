/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarCategory
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# The original unit-coefficient category maps to every SAME scalar category

Evaluate each complete original unit-shaped Hom map at the same unit
simplex. The source is the canonical ForgetEnrichment category; the
target is the existing original SSet.ScalarObject category. The full
original identity and composition equations make this an actual functor,
retaining independent coefficient and object universes.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory

namespace SSet
variable (C : Type v) [EnrichedCategory SSet.{u} C]

/-- The SAME original whole unit coefficient maps to its unchanged simplex in every original
scalar category. -/
def unitScalarFunctor (q : SimplexCategoryᵒᵖ) :
    ForgetEnrichment SSet.{u} C ⥤ ScalarObject C q where
  obj x := ⟨ForgetEnrichment.to SSet.{u} x⟩
  map f := (ForgetEnrichment.homTo SSet.{u} f).app q PUnit.unit
  map_id x := congrArg (fun h => h.app q PUnit.unit) (ForgetEnrichment.homTo_id SSet.{u} x)
  map_comp f g := congrArg (fun h => h.app q PUnit.unit) (ForgetEnrichment.homTo_comp SSet.{u} f g)

/-- Every actual original unit-shaped map retains its literal scalar coefficient. -/
theorem unitScalarFunctor_map (q : SimplexCategoryᵒᵖ)
    {x y : ForgetEnrichment SSet.{u} C} (f : x ⟶ y) :
    (unitScalarFunctor C q).map f = (ForgetEnrichment.homTo SSet.{u} f).app q PUnit.unit := rfl

/-- The original object label is unchanged by this genuine unit-to-scalar functor. -/
theorem unitScalarFunctor_obj (q : SimplexCategoryᵒᵖ) (x : ForgetEnrichment SSet.{u} C) :
    ((unitScalarFunctor C q).obj x).obj = ForgetEnrichment.to SSet.{u} x := rfl

end SSet
