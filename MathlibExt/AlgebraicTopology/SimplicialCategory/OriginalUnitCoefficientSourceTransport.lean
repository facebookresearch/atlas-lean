/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnitCoefficientReadback

/-!
# Exact original source equality transport of full unit coefficients

Transport along a proved source-object equality retains the whole
original unit coefficient and exact original image equation.
The proof eliminates only its stated equality in the
plain enriched category. All original object universes stay independent.
-/

noncomputable section
universe u v w
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.OriginalUnitCoefficientReadback
variable {E : Type v} [EnrichedCategory SSet.{u} E]
variable {D : Type w} [EnrichedCategory SSet.{u} D]

/-- The SAME source transport retains the entire original coefficient image through the original functor and target
equality. -/
theorem source_transport_image (r : EnrichedFunctor SSet.{u} E D)
    {x x' y : E} (h : x = x') (d : D) (hy : r.obj y = d)
    (q : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y)) :
    (q ≫ eqToHom (congrArg₂ (fun s t : E => s ⟶[SSet.{u}] t) h rfl)) ≫
      (r.map x' y ≫ eqToHom (congrArg₂ (fun s t : D => s ⟶[SSet.{u}] t) rfl hy)) =
      q ≫ (r.map x y ≫ eqToHom (congrArg₂ (fun s t : D => s ⟶[SSet.{u}] t)
        (congrArg r.obj h) hy)) := by
  cases h
  exact congrArg (fun k => k ≫ (r.map x y ≫ eqToHom
    (congrArg₂ (fun s t : D => s ⟶[SSet.{u}] t) rfl hy))) (Category.comp_id q)

end CategoryTheory.SimplicialEnrichment.OriginalUnitCoefficientReadback
