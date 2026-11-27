/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# Actual enriched Hom maps at equal original endpoints

The same enriched functor map is followed by the exact supplied object
endpoint equalities. Composition and whole-functor equality retain these
literal maps. The base category object/Hom universes and each enriched
source/intermediate/target object universe are independent.
-/

@[expose] public section

noncomputable section

universe uV vV uC uD uE

open CategoryTheory MonoidalCategory

namespace CategoryTheory.EnrichedFunctor

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
    {C : Type uC} {D : Type uD} {E : Type uE}
    [EnrichedCategory V C] [EnrichedCategory V D] [EnrichedCategory V E]

/-- The SAME actual enriched functor Hom map at the supplied original equal endpoint objects. -/
def homMap (F : EnrichedFunctor V C D) {x y : C} {a b : D}
    (hx : F.obj x = a) (hy : F.obj y = b) : (x ⟶[V] y) ⟶ (a ⟶[V] b) :=
  F.map x y ≫ eqToHom (congrArg₂ (fun a b : D => a ⟶[V] b) hx hy)

/-- The SAME entire enriched functor equality retains its literal original endpoint Hom maps. -/
theorem homMap_eq {F G : EnrichedFunctor V C D} (h : F = G) {x y : C} {a b : D}
    (hx : F.obj x = a) (hy : F.obj y = b) (hx' : G.obj x = a) (hy' : G.obj y = b) :
    homMap F hx hy = homMap G hx' hy' := by
  cases h
  rfl

/-- Both SAME actual enriched functor Hom maps compose with the original endpoint equality
formulas. -/
theorem homMap_comp (F : EnrichedFunctor V C D) (G : EnrichedFunctor V D E)
    {x y : C} {a b : D} {c d : E} (hx : F.obj x = a) (hy : F.obj y = b)
    (ha : G.obj a = c) (hb : G.obj b = d) :
    homMap F hx hy ≫ homMap G ha hb =
      homMap (F.comp V G) ((congrArg G.obj hx).trans ha) ((congrArg G.obj hy).trans hb) := by
  subst a
  subst b
  change (F.map x y ≫ 𝟙 _) ≫ (G.map (F.obj x) (F.obj y) ≫
    eqToHom (congrArg₂ (fun c d : E => c ⟶[V] d) ha hb)) =
      (F.map x y ≫ G.map (F.obj x) (F.obj y)) ≫
        eqToHom (congrArg₂ (fun c d : E => c ⟶[V] d) ha hb)
  rw [Category.comp_id, Category.assoc]

/-- The SAME actual enriched identity has the original literal identity Hom map. -/
theorem homMap_id (x y : C) :
    homMap (EnrichedFunctor.id V C) (x := x) (y := y) rfl rfl = 𝟙 (x ⟶[V] y) :=
  Category.id_comp _

end CategoryTheory.EnrichedFunctor
