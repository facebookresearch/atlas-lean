/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ConnectedComponents.Products
import MathlibExt.CategoryTheory.Enriched.TransportFunctor

/-!
# The original component Hom category of a simplicial enrichment

The genuine finite-product component functor transports the original
enrichment to Types. Its honest ordinary category has the same individual
original objects and component classes only in its Hom sets. Original
strict enriched maps induce actual ordinary functors, with literal
component-map readback and identity/composition laws.
-/

noncomputable section
universe u v w z
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.ComponentCategory

/-- The same individual original object type with component classes solely in its Hom sets. -/
abbrev objects (C : Type v) := TransportEnrichment SSet.π₀Functor.{u} C

/-- Read the same individual original component-category object. -/
def originalObject (C : Type v) (x : C) : C := x

/-- The supplied individual original object, regarded in the actual component Hom category. -/
def objectOf (C : Type v) (x : C) : objects.{u} C := x

variable (C : Type v) [EnrichedCategory SSet.{u} C]

/-- The honest ordinary component Hom category of the supplied original enrichment. -/
instance category : Category.{u} (objects.{u} C) := categoryOfEnrichedCategoryType _

/-- Its actual ordinary Hom set is the original enriched Hom's component set, with the original endpoints retained. -/
theorem hom_eq (x y : objects.{u} C) :
    (x ⟶ y) = SSet.π₀ (originalObject C x ⟶[SSet.{u}] originalObject C y) := rfl

/-- The component arrow represented by a supplied individual original Hom vertex. -/
def arrowOf {x y : C} (a : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    objectOf.{u} C x ⟶ objectOf.{u} C y := SSet.π₀.mk a

variable {C} {D : Type w} [EnrichedCategory SSet.{u} D] {E : Type z} [EnrichedCategory SSet.{u} E]

/-- The same original enriched map induces an actual ordinary component Hom functor. -/
def mapFunctor (F : EnrichedFunctor SSet.{u} C D) : objects.{u} C ⥤ objects.{u} D where
  obj x := F.obj x
  map {x y} a := SSet.mapπ₀ (F.map x y) a
  map_id x := by
    let G := EnrichedFunctor.transportBase SSet.π₀Functor F
    exact congr($(G.map_id x) PUnit.unit)
  map_comp {x y z} a b := by
    let G := EnrichedFunctor.transportBase SSet.π₀Functor F
    exact congr($(G.map_comp x y z) (a, b))

/-- The actual ordinary component functor keeps precisely the original object map. -/
theorem mapFunctor_obj (F : EnrichedFunctor SSet.{u} C D) (x : C) :
    (mapFunctor F).obj x = F.obj x := rfl

/-- The actual ordinary component map is the same original Hom-component map. -/
theorem mapFunctor_map (F : EnrichedFunctor SSet.{u} C D) (x y : C) (a : SSet.π₀ (x ⟶[SSet.{u}] y)) :
    (mapFunctor F).map a = SSet.mapπ₀ (F.map x y) a := rfl

/-- Every original represented vertex arrow reads back to its actual original image vertex. -/
theorem mapFunctor_arrowOf (F : EnrichedFunctor SSet.{u} C D) {x y : C}
    (a : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    (mapFunctor F).map (arrowOf C a) = arrowOf D ((F.map x y).app (op ⦋0⦌) a) :=
  SSet.mapπ₀_mk _ _

/-- The actual ordinary component functor preserves the same original enriched identity. -/
theorem mapFunctor_id : mapFunctor (EnrichedFunctor.id SSet.{u} C) = 𝟭 (objects.{u} C) := by
  refine Functor.hext (F := mapFunctor (EnrichedFunctor.id SSet.{u} C))
    (G := 𝟭 (objects.{u} C)) (fun _ => rfl) (fun x y a => ?_)
  apply heq_of_eq
  change SSet.mapπ₀ (𝟙 (originalObject C x ⟶[SSet.{u}] originalObject C y)) a = a
  exact SSet.mapπ₀_id_apply a

/-- The actual ordinary component functor preserves composition of the same original enriched maps. -/
theorem mapFunctor_comp (F : EnrichedFunctor SSet.{u} C D) (G : EnrichedFunctor SSet.{u} D E) :
    mapFunctor (EnrichedFunctor.comp SSet.{u} F G) = mapFunctor F ⋙ mapFunctor G := by
  refine Functor.hext (F := mapFunctor (EnrichedFunctor.comp SSet.{u} F G))
    (G := mapFunctor F ⋙ mapFunctor G) (fun _ => rfl) (fun x y a => ?_)
  apply heq_of_eq
  change SSet.mapπ₀ (F.map (originalObject C x) (originalObject C y) ≫
      G.map (F.obj (originalObject C x)) (F.obj (originalObject C y))) a =
    SSet.mapπ₀ (G.map (F.obj (originalObject C x)) (F.obj (originalObject C y)))
      (SSet.mapπ₀ (F.map (originalObject C x) (originalObject C y)) a)
  exact SSet.mapπ₀_comp_apply _ _ _

end CategoryTheory.SimplicialEnrichment.ComponentCategory
