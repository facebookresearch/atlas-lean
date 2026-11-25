/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.HomEndpointMaps

/-!
# The actual enriched endpoint-map square

The existing full enriched Hom map retains both original source and
target endpoint equations. Equality of those endpoint labels gives
the whole original square, at independent coefficient and object
universes.
-/

@[expose] public section

noncomputable section

universe uV vV uC uD

open CategoryTheory MonoidalCategory

namespace CategoryTheory.EnrichedFunctor

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} {D : Type uD} [EnrichedCategory V C] [EnrichedCategory V D]

/-- The same full original enriched Hom maps commute with both original source and target
endpoint equalities. -/
theorem homMap_endpoint_square (F : EnrichedFunctor V C D)
    {x y x' y' : C} {a b a' b' : D}
    (hx : x = x') (hy : y = y') (ha : a = a') (hb : b = b')
    (hFx : F.obj x = a) (hFy : F.obj y = b)
    (hFx' : F.obj x' = a') (hFy' : F.obj y' = b') :
    eqToHom (congrArg₂ (fun x y : C => x ⟶[V] y) hx hy) ≫ homMap F hFx' hFy' =
      homMap F hFx hFy ≫ eqToHom (congrArg₂ (fun a b : D => a ⟶[V] b) ha hb) := by
  cases hx
  cases hy
  cases ha
  cases hb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end CategoryTheory.EnrichedFunctor
