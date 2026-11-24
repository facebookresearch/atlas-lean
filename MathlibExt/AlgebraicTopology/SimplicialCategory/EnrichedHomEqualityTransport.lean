/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.StrictCategory
import MathlibExt.CategoryTheory.Enriched.HomEqualityTransport

/-!
# Exact original Hom transports from whole functor and endpoint equalities

Only actual original object equations transport the endpoints of the
SAME full enriched Hom maps. These elementary equations retain every
Hom operator and support original changing-object arrow retracts.
-/

noncomputable section
universe u v w
open CategoryTheory

namespace CategoryTheory.EnrichedFunctor

variable {C : Type v} [EnrichedCategory SSet.{u} C]
variable {D : Type w} [EnrichedCategory SSet.{u} D]

/-- Equality of the SAME whole original enriched functors transports each full Hom through
precisely its original
object equations. -/
theorem homMap_transport_of_eq {F G : EnrichedFunctor SSet.{u} C D} (h : F = G) (x y : C) :
    F.map x y ≫ eqToHom (congrArg₂ (fun a b : D => (a ⟶[SSet.{u}] b))
      (congrArg (fun H => H.obj x) h) (congrArg (fun H => H.obj y) h)) = G.map x y := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]

/-- The SAME original Hom map commutes with transports from its two actual original source
endpoint equations. -/
theorem homMap_endpoint_transport (F : EnrichedFunctor SSet.{u} C D)
    {x y x' y' : C} (hx : x = x') (hy : y = y') :
    eqToHom (congrArg₂ (fun a b : C => (a ⟶[SSet.{u}] b)) hx hy) ≫ F.map x' y' =
      F.map x y ≫ eqToHom (congrArg₂ (fun a b : D => (a ⟶[SSet.{u}] b))
        (congrArg F.obj hx) (congrArg F.obj hy)) :=
  (EnrichedHomEqualityTransport.functor_map F hx hy).symm

end CategoryTheory.EnrichedFunctor
