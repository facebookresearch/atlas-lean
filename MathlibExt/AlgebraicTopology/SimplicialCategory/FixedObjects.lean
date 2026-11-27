/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.StrictCategory
import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
# Simplicial enrichments with fixed original objects

The fiber of the object-forgetting functor retains every individual object
label. Its arrows are genuine enriched functors over the identity of that
object type. Hom evaluation uses the original Hom map and only the two
endpoint equality transports.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment

/-- Forget only the enrichment, retaining the original object type and object maps. -/
def forgetObjects : Carrier.{u} ⥤ Type u where
  obj C := C
  map F := ↾F.obj

/-- The existing functor fiber, with strict identity-on-object enriched maps. -/
abbrev FixedObjects (O : Type u) := Functor.Fiber forgetObjects O

namespace FixedObjects

variable {O : Type u}

/-- The individual original vertex carrying the supplied fixed object label. -/
def vertex (C : FixedObjects O) (x : O) : C.val :=
  (eqToHom C.property.symm) x

/-- Bundle an enrichment on the literal supplied object type. -/
def of (O : Type u) [EnrichedCategory SSet.{u} O] : FixedObjects O :=
  ⟨SimplicialEnrichment.of O, rfl⟩

/-- Literal enrichments retain every original label without an object quotient. -/
@[simp]
theorem vertex_of (O : Type u) [EnrichedCategory SSet.{u} O] (x : O) :
    vertex (of O) x = x := rfl

/-- An arrow of the fiber preserves the individual supplied label exactly. -/
theorem map_vertex {C D : FixedObjects O} (F : C ⟶ D) (x : O) :
    F.val.obj (vertex C x) = vertex D x := by
  have : forgetObjects.IsHomLift (𝟙 O) F.val := F.property
  have h : forgetObjects.map F.val = eqToHom C.property ≫ eqToHom D.property.symm := by
    simpa only [Category.id_comp] using IsHomLift.fac' forgetObjects (𝟙 O) F.val
  have hc : eqToHom C.property.symm ≫ forgetObjects.map F.val =
      eqToHom D.property.symm := by
    rw [h, ← Category.assoc, eqToHom_trans]
    simp
  change (eqToHom C.property.symm ≫ forgetObjects.map F.val) x =
    (eqToHom D.property.symm) x
  exact congrArg (fun k => k x) hc

/-- The original scalar Hom object at two individual fixed labels. -/
abbrev hom (C : FixedObjects O) (x y : O) : SSet.{u} :=
  vertex C x ⟶[SSet.{u}] vertex C y

/-- The actual enriched Hom map followed by the proved endpoint equalities. -/
def homMap {C D : FixedObjects O} (F : C ⟶ D) (x y : O) :
    hom C x y ⟶ hom D x y :=
  F.val.map (vertex C x) (vertex C y) ≫
    eqToHom (by change _ = (vertex D x ⟶[SSet.{u}] vertex D y)
                rw [map_vertex F x, map_vertex F y])

private theorem map_eqToHom {C D : Carrier.{u}} (F : C ⟶ D)
    {x y x' y' : C} (hx : x = x') (hy : y = y') :
    eqToHom (by rw [hx, hy] : (x ⟶[SSet.{u}] y) = (x' ⟶[SSet.{u}] y')) ≫
        F.map x' y' =
      F.map x y ≫ eqToHom (by rw [hx, hy]) := by
  cases hx
  cases hy
  simp

/-- Evaluation preserves the literal enriched identity on every Hom object. -/
@[simp]
theorem homMap_id (C : FixedObjects O) (x y : O) :
    homMap (𝟙 C) x y = 𝟙 (hom C x y) := by
  change 𝟙 _ ≫ eqToHom _ = 𝟙 _
  simp

/-- Evaluation preserves composition of the same original enriched maps. -/
@[simp]
theorem homMap_comp {C D E : FixedObjects O} (F : C ⟶ D) (G : D ⟶ E)
    (x y : O) : homMap (F ≫ G) x y = homMap F x y ≫ homMap G x y := by
  have ht := map_eqToHom G.val (map_vertex F x) (map_vertex F y)
  have hc := congrArg (fun k => k ≫
    eqToHom (by rw [map_vertex G x, map_vertex G y])) ht
  have h := congrArg (fun k => F.val.map (vertex C x) (vertex C y) ≫ k) hc
  change (F.val.map (vertex C x) (vertex C y) ≫
      G.val.map (F.val.obj (vertex C x)) (F.val.obj (vertex C y))) ≫ eqToHom _ =
    (F.val.map (vertex C x) (vertex C y) ≫ eqToHom _) ≫
      G.val.map (vertex D x) (vertex D y) ≫ eqToHom _
  simpa only [Category.assoc, eqToHom_trans] using h.symm

/-- Hom evaluation on the actual fixed-object category. -/
def evaluation (x y : O) : FixedObjects O ⥤ SSet.{u} where
  obj C := hom C x y
  map F := homMap F x y
  map_id C := homMap_id C x y
  map_comp F G := homMap_comp F G x y

end FixedObjects
end CategoryTheory.SimplicialEnrichment
