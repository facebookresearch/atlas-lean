/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.StrictCategory

/-!
# Entire original Hom isomorphisms of strict enriched isomorphisms

Both actual enriched inverse maps retain every original Hom simplex.
The strict object round trips give precisely the required endpoint
equality transports. The two whole enriched inverse equations prove
the same full Hom isomorphism through those actual maps.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment

/-- Equality of entire enriched functors gives the same original Hom map with its actual
target endpoint transports. -/
theorem functorHom_congr {C D : Carrier.{u}} {F G : C ⟶ D} (h : F = G) (x y : C) :
    F.map x y ≫ eqToHom (congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b)
      (congrArg (fun f : C ⟶ D => f.obj x) h) (congrArg (fun f : C ⟶ D => f.obj y) h)) =
      G.map x y := by
  subst G
  exact Category.comp_id _

/-- Changing the two actual source endpoint labels retains precisely the same entire
enriched Hom map. -/
theorem functorHom_source_congr {C D : Carrier.{u}} (F : C ⟶ D)
    {x x' y y' : C} (hx : x = x') (hy : y = y') :
    eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b) hx hy) ≫ F.map x' y' =
      F.map x y ≫ eqToHom (congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b)
        (congrArg F.obj hx) (congrArg F.obj hy)) := by
  subst x'
  subst y'
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The actual enriched forward-inverse object round trip retains the original individual
source object. -/
theorem strictIso_hom_inv_obj {C D : Carrier.{u}} (e : C ≅ D) (x : C) :
    e.inv.obj (e.hom.obj x) = x :=
  congrArg (fun f : C ⟶ C => f.obj x) e.hom_inv_id

/-- The actual enriched inverse-forward object round trip retains the original individual
target object. -/
theorem strictIso_inv_hom_obj {C D : Carrier.{u}} (e : C ≅ D) (x : D) :
    e.hom.obj (e.inv.obj x) = x :=
  congrArg (fun f : D ⟶ D => f.obj x) e.inv_hom_id

/-- The complete original Hom isomorphism uses the actual enriched forward map and inverse
map with their strict
original endpoint transports. -/
def isoHomIso {C D : Carrier.{u}} (e : C ≅ D) (x y : C) :
    (x ⟶[SSet.{u}] y) ≅ (e.hom.obj x ⟶[SSet.{u}] e.hom.obj y) where
  hom := e.hom.map x y
  inv := e.inv.map (e.hom.obj x) (e.hom.obj y) ≫
    eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b)
      (strictIso_hom_inv_obj e x) (strictIso_hom_inv_obj e y))
  hom_inv_id := by
    have h := functorHom_congr e.hom_inv_id x y
    change (e.hom.map x y ≫ e.inv.map (e.hom.obj x) (e.hom.obj y)) ≫
      eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b)
        (strictIso_hom_inv_obj e x) (strictIso_hom_inv_obj e y)) = 𝟙 _ at h
    exact (Category.assoc _ _ _).symm.trans h
  inv_hom_id := by
    have h := functorHom_congr e.inv_hom_id (e.hom.obj x) (e.hom.obj y)
    have ht := functorHom_source_congr e.hom (strictIso_hom_inv_obj e x) (strictIso_hom_inv_obj e y)
    change (e.inv.map (e.hom.obj x) (e.hom.obj y) ≫
      e.hom.map (e.inv.obj (e.hom.obj x)) (e.inv.obj (e.hom.obj y))) ≫
      eqToHom (congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b)
        (congrArg e.hom.obj (strictIso_hom_inv_obj e x))
        (congrArg e.hom.obj (strictIso_hom_inv_obj e y))) = 𝟙 _ at h
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => e.inv.map (e.hom.obj x) (e.hom.obj y) ≫ f) ht).trans
        ((Category.assoc _ _ _).symm.trans h))

/-- The original strict-Hom name retains the canonical full Hom isomorphism and both actual maps. -/
abbrev strictIsoHom {C D : Carrier.{u}} (e : C ≅ D) (x y : C) :
    (x ⟶[SSet.{u}] y) ≅ (e.hom.obj x ⟶[SSet.{u}] e.hom.obj y) :=
  isoHomIso e x y

end CategoryTheory.SimplicialEnrichment
