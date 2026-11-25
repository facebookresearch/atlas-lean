/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory.Restriction
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Nat.Defs

/-!# Actual restriction components and arbitrary pointwise properties -/
set_option autoImplicit false
universe uD vD uE vE uS vS uM vM uJ
open CategoryTheory Functor MorphismProperty

namespace MathlibExtTest.PointwiseRestriction

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {S : Type uS} [Category.{vS} S] {M : Type uM} [Category.{vM} M]

example (P : MorphismProperty M) (u : D ⥤ E) :
    P.functorCategory E ≤
      (P.functorCategory D).inverseImage ((whiskeringLeft D E M).obj u) :=
  functorCategory_le_inverseImage_whiskeringLeft P u

example (P : MorphismProperty M) (u : D ⥤ E) {X Y : E ⥤ M}
    (f : X ⟶ Y) (hf : P.functorCategory E f) :
    P.functorCategory D (((whiskeringLeft D E M).obj u).map f) :=
  functorCategory_le_inverseImage_whiskeringLeft P u f hf

example (u : D ⥤ E) (X : E ⥤ M) :
    ((whiskeringLeft D E M).obj u).obj X = u ⋙ X := rfl

example (u : D ⥤ E) (X : E ⥤ M) {d d' : D} (a : d ⟶ d') :
    (((whiskeringLeft D E M).obj u).obj X).map a = X.map (u.map a) := rfl

example (u : D ⥤ E) {X Y : E ⥤ M} :
    (fun (f : X ⟶ Y) (d : D) => (((whiskeringLeft D E M).obj u).map f).app d) =
      fun (f : X ⟶ Y) (d : D) => f.app (u.obj d) := rfl

example (u : D ⥤ E) {X Y : E ⥤ M} (f : X ⟶ Y) {d d' : D} (a : d ⟶ d') :
    X.map (u.map a) ≫ f.app (u.obj d') = f.app (u.obj d) ≫ Y.map (u.map a) :=
  f.naturality (u.map a)

example (u : D ⥤ E) (X : E ⥤ M) :
    ((whiskeringLeft D E M).obj u).map (𝟙 X) = 𝟙 (u ⋙ X) :=
  ((whiskeringLeft D E M).obj u).map_id X

example (u : D ⥤ E) {X Y Z : E ⥤ M} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((whiskeringLeft D E M).obj u).map (f ≫ g) =
      ((whiskeringLeft D E M).obj u).map f ≫ ((whiskeringLeft D E M).obj u).map g :=
  ((whiskeringLeft D E M).obj u).map_comp f g

example : (whiskeringLeft D D M).obj (𝟭 D) = 𝟭 (D ⥤ M) :=
  whiskeringLeft_obj_id

example (u : D ⥤ E) (v : E ⥤ S) :
    (whiskeringLeft D S M).obj (u ⋙ v) =
      (whiskeringLeft E S M).obj v ⋙ (whiskeringLeft D E M).obj u :=
  whiskeringLeft_obj_comp u v

example (P : MorphismProperty M) (u : D ⥤ E) (v : E ⥤ S)
    {X Y : S ⥤ M} (f : X ⟶ Y) (hf : P.functorCategory S f) :
    P.functorCategory D (((whiskeringLeft D S M).obj (u ⋙ v)).map f) :=
  functorCategory_le_inverseImage_whiskeringLeft P (u ⋙ v) f hf

example {J : Type uJ} (P : J → MorphismProperty M) (u : D ⥤ E)
    {X Y : E ⥤ M} (f : X ⟶ Y) (hf : ∀ j : J, (P j).functorCategory E f) :
    ∀ j : J, (P j).functorCategory D (((whiskeringLeft D E M).obj u).map f) := by
  intro j
  exact functorCategory_le_inverseImage_whiskeringLeft (P j) u f (hf j)

example (P Q : MorphismProperty M) (u : D ⥤ E) {X Y : E ⥤ M}
    (f : X ⟶ Y) (hf : (P ⊓ Q).functorCategory E f) :
    (P ⊓ Q).functorCategory D (((whiskeringLeft D E M).obj u).map f) :=
  functorCategory_le_inverseImage_whiskeringLeft (P ⊓ Q) u f hf

example (u : D ⥤ E) {X Y : E ⥤ M} (f : X ⟶ Y)
    (hf : (isomorphisms M).functorCategory E f) :
    (isomorphisms M).functorCategory D (((whiskeringLeft D E M).obj u).map f) :=
  functorCategory_le_inverseImage_whiskeringLeft (isomorphisms M) u f hf

example (P : MorphismProperty M) (u : Discrete PEmpty.{1} ⥤ E)
    {X Y : E ⥤ M} (f : X ⟶ Y) :
    P.functorCategory (Discrete PEmpty.{1})
      (((whiskeringLeft (Discrete PEmpty.{1}) E M).obj u).map f) := by
  intro d
  exact d.as.elim

example (P : MorphismProperty M) (u : Discrete ℕ ⥤ E) {X Y : E ⥤ M}
    (f : X ⟶ Y) (hf : P.functorCategory E f) :
    P.functorCategory (Discrete ℕ) (((whiskeringLeft (Discrete ℕ) E M).obj u).map f) :=
  functorCategory_le_inverseImage_whiskeringLeft P u f hf

example (u : SingleObj (Multiplicative ℕ) ⥤ E) {X Y : E ⥤ M} (f : X ⟶ Y)
    {d d' : SingleObj (Multiplicative ℕ)} (a : d ⟶ d') :
    X.map (u.map a) ≫ f.app (u.obj d') = f.app (u.obj d) ≫ Y.map (u.map a) :=
  f.naturality (u.map a)

section Raised

local instance : Category.{vD} (ULift.{uD + 1} D) := uliftCategory D
local instance : Category.{max (vD + 1) vD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  @ULiftHom.category (ULift.{uD + 1} D) (inferInstance : Category.{vD} (ULift.{uD + 1} D))
local instance : Category.{vE} (ULift.{uE + 1} E) := uliftCategory E
local instance : Category.{max (vE + 1) vE} (ULiftHom.{vE + 1} (ULift.{uE + 1} E)) :=
  @ULiftHom.category (ULift.{uE + 1} E) (inferInstance : Category.{vE} (ULift.{uE + 1} E))

example (P : MorphismProperty M)
    (u : ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ ULiftHom.{vE + 1} (ULift.{uE + 1} E)) :
    P.functorCategory (ULiftHom.{vE + 1} (ULift.{uE + 1} E)) ≤
      (P.functorCategory (ULiftHom.{vD + 1} (ULift.{uD + 1} D))).inverseImage
        ((whiskeringLeft _ _ M).obj u) :=
  functorCategory_le_inverseImage_whiskeringLeft P u

end Raised
end MathlibExtTest.PointwiseRestriction
