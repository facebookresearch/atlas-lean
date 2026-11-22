/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectPrecompositionNaturality

/-!
# The original fixed-label Hom map preserves actual component equivalences

The SAME actual full enriched-functor image is invertible on components.
Its two proved original endpoint equalities transport the unchanged full
unit coefficient to the actual fixed target labels. No component-equivalence
outcome or Kan condition for the target is assumed.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.EnrichedHomPrecomposition
open ComponentCategory
variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- Actual endpoint equality transport preserves invertibility of the SAME original unit coefficient component arrow. -/
theorem unit_endpoint_isIso {x y x' y' : C} (hx : x = x') (hy : y = y')
    (q : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y))
    (hq : IsIso (arrowOf C (SSet.unitHomEquiv _ q))) :
    IsIso (arrowOf C (SSet.unitHomEquiv _
      (q ≫ eqToHom (congrArg₂ (fun s t : C => s ⟶[SSet.{u}] t) hx hy)))) := by
  cases hx
  cases hy
  have he : q ≫ eqToHom (congrArg₂ (fun s t : C => s ⟶[SSet.{u}] t) rfl rfl) = q :=
    Category.comp_id _
  exact (congrArg (fun a => IsIso (arrowOf C (SSet.unitHomEquiv _ a))) he).mpr hq

end CategoryTheory.SimplicialEnrichment.EnrichedHomPrecomposition

namespace CategoryTheory.SimplicialEnrichment.FixedObjects
open ComponentCategory EnrichedHomPrecomposition EnrichedHomActionNaturality
variable {O : Type u} {P A : FixedObjects O}

/-- The SAME full fixed-label Hom image retains the actual original component equivalence under both genuine endpoint
equations. -/
theorem homMap_unit_isIso (F : P ⟶ A) (x y : O)
    (q : 𝟙_ SSet.{u} ⟶ hom P x y)
    (hq : IsIso (arrowOf P.val (SSet.unitHomEquiv _ q))) :
    IsIso (arrowOf A.val (SSet.unitHomEquiv _ (q ≫ homMap F x y))) := by
  let _ : IsIso (arrowOf P.val (SSet.unitHomEquiv _ q)) := hq
  have hraw : IsIso (arrowOf A.val
      (SSet.unitHomEquiv _ (q ≫ F.val.map (vertex P x) (vertex P y)))) :=
    (congrArg IsIso (component_map_unit F.val q)).mp inferInstance
  have ht := unit_endpoint_isIso (map_vertex F x) (map_vertex F y)
    (q ≫ F.val.map (vertex P x) (vertex P y)) hraw
  exact (congrArg (fun k : 𝟙_ SSet.{u} ⟶ hom A x y =>
    IsIso (arrowOf A.val (SSet.unitHomEquiv _ k))) (Category.assoc _ _ _)).mp ht

end CategoryTheory.SimplicialEnrichment.FixedObjects
