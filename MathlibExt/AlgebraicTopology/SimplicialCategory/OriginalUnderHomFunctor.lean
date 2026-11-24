/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.StrictCategory
import MathlibExt.CategoryTheory.Enriched.HomEqualityTransport
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The SAME full original Hom functor under a changing-object enrichment

The two supplied original source objects retain their actual images
under every whole original functor. Each morphism acts by its complete
original Hom map, transported only through the true original Under
triangle. Identity and composition retain these SAME original maps.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.OriginalUnderHom

variable (C : Carrier.{u}) (x y : C)

/-- The SAME full original Hom at the actual images of the original source pair. -/
abbrev object (U : Under C) : SSet.{u} := U.hom.obj x ⟶[SSet.{u}] U.hom.obj y

/-- The actual original triangle retains its SAME individual endpoint image. -/
theorem endpoint {U V : Under C} (f : U ⟶ V) (a : C) :
    f.right.obj (U.hom.obj a) = V.hom.obj a :=
  congrArg (fun F : C ⟶ V.right => F.obj a) (Under.w f)

/-- The complete original Hom map with only the actual two endpoint equations. -/
def map {U V : Under C} (f : U ⟶ V) : object C x y U ⟶ object C x y V :=
  f.right.map (U.hom.obj x) (U.hom.obj y) ≫
    eqToHom (congrArg₂ (fun a b : V.right => a ⟶[SSet.{u}] b) (endpoint C f x) (endpoint C f y))

/-- The SAME original identity map is retained on every complete original Hom. -/
theorem map_id (U : Under C) : map C x y (𝟙 U) = 𝟙 (object C x y U) := by
  let t : object C x y U = object C x y U :=
    congrArg₂ (fun a b : U.right => a ⟶[SSet.{u}] b) (endpoint C (𝟙 U) x) (endpoint C (𝟙 U) y)
  change 𝟙 (object C x y U) ≫ eqToHom t = 𝟙 (object C x y U)
  rw [eqToHom_refl, Category.comp_id]

/-- Both complete original Under maps compose to the SAME original coefficient map. -/
theorem map_comp {U V W : Under C} (f : U ⟶ V) (g : V ⟶ W) :
    map C x y (f ≫ g) = map C x y f ≫ map C x y g := by
  let tf := congrArg₂ (fun a b : V.right => a ⟶[SSet.{u}] b) (endpoint C f x) (endpoint C f y)
  let tg := congrArg₂ (fun a b : W.right => a ⟶[SSet.{u}] b) (endpoint C g x) (endpoint C g y)
  let tr := congrArg₂ (fun a b : W.right => a ⟶[SSet.{u}] b)
    (congrArg g.right.obj (endpoint C f x)) (congrArg g.right.obj (endpoint C f y))
  let tc := congrArg₂ (fun a b : W.right => a ⟶[SSet.{u}] b) (endpoint C (f ≫
    g) x) (endpoint C (f ≫ g) y)
  have ht : eqToHom tf ≫ g.right.map (V.hom.obj x) (V.hom.obj y) =
      g.right.map (f.right.obj (U.hom.obj x)) (f.right.obj (U.hom.obj y)) ≫ eqToHom tr :=
    (EnrichedHomEqualityTransport.functor_map g.right (endpoint C f x) (endpoint C f y)).symm
  have h := congrArg (fun a => f.right.map (U.hom.obj x) (U.hom.obj y) ≫ a ≫ eqToHom tg) ht
  change (f.right.map (U.hom.obj x) (U.hom.obj y) ≫
    g.right.map (f.right.obj (U.hom.obj x)) (f.right.obj (U.hom.obj y))) ≫ eqToHom tc =
      (f.right.map (U.hom.obj x) (U.hom.obj y) ≫ eqToHom tf) ≫
        (g.right.map (V.hom.obj x) (V.hom.obj y) ≫ eqToHom tg)
  simpa only [Category.assoc, eqToHom_trans] using h.symm

/-- The actual complete original Hom functor on the SAME original Under category. -/
def functor : Under C ⥤ SSet.{u} where
  obj := object C x y
  map := map C x y
  map_id := map_id C x y
  map_comp := map_comp C x y

/-- The complete original Under-morphism Hom map is read back literally. -/
theorem functor_map {U V : Under C} (f : U ⟶ V) :
    (functor C x y).map f = map C x y f := rfl

end CategoryTheory.SimplicialEnrichment.OriginalUnderHom
