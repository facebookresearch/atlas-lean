/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.TrivialBundleWithFiberOver

set_option autoImplicit false

open CategoryTheory Limits

universe v u

namespace MathlibExtTest.CategoryTheory.TrivialBundleWithFiberTransportTests

variable {C : Type u} [Category.{v} C]

example {F E E' B : C} {p : E ⟶ B} {p' : E' ⟶ B}
    (e : E ≅ E') (heq : e.hom ≫ p' = p)
    (h : TrivialBundleWithFiber F p) :
    (TrivialBundleWithFiber.ofIso_rev e heq h).r = e.symm.hom ≫ h.r :=
  rfl

example {F G E B : C} {p : E ⟶ B}
    (e : F ≅ G) (h : TrivialBundleWithFiber G p) :
    (TrivialBundleWithFiber.mapFiber e h).r = h.r ≫ e.inv :=
  rfl

example {F E B B' : C} {p : E ⟶ B} {f : B' ⟶ B}
    (h : MorphismProperty.TrivialBundleWithFiberOver F p f)
    {E'' : C} {q : E'' ⟶ B'} {s : E'' ⟶ E}
    (sq2 : IsPullback s q p f) (e : E'' ≅ h.E')
    (heq : e.hom ≫ h.p' = q) :
    (MorphismProperty.TrivialBundleWithFiberOver.ofIso h sq2 e heq).trivial.r =
      e.hom ≫ h.trivial.r :=
  rfl

example {F E B B' : C} {p : E ⟶ B} {f : B' ⟶ B}
    (h : MorphismProperty.TrivialBundleWithFiberOver F p f)
    {E'' : C} {q : E'' ⟶ B'} {s : E'' ⟶ E}
    (sq2 : IsPullback s q p f) (e : E'' ≅ h.E')
    (heq : e.hom ≫ h.p' = q) :
    (MorphismProperty.TrivialBundleWithFiberOver.ofIso h sq2 e heq).p' = q :=
  rfl

example {F E B B' : C} {p : E ⟶ B} {f : B' ⟶ B}
    (h : MorphismProperty.TrivialBundleWithFiberOver F p f)
    {E'' : C} {q : E'' ⟶ B'} {s : E'' ⟶ E}
    (sq2 : IsPullback s q p f) (e : E'' ≅ h.E')
    (heq : e.hom ≫ h.p' = q) :
    (MorphismProperty.TrivialBundleWithFiberOver.ofIso h sq2 e heq).t = s :=
  rfl

example {F G E B B' : C} {p : E ⟶ B} {f : B' ⟶ B}
    (e : F ≅ G) (h : MorphismProperty.TrivialBundleWithFiberOver G p f) :
    (MorphismProperty.TrivialBundleWithFiberOver.mapFiber e h).trivial.r =
      h.trivial.r ≫ e.inv :=
  rfl

example {F G E B B' : C} {p : E ⟶ B} {f : B' ⟶ B}
    (e : F ≅ G) (h : MorphismProperty.TrivialBundleWithFiberOver G p f) :
    (MorphismProperty.TrivialBundleWithFiberOver.mapFiber e h).p' = h.p' :=
  rfl

example {F G E B B' : C} {p : E ⟶ B} {f : B' ⟶ B}
    (e : F ≅ G) (h : MorphismProperty.TrivialBundleWithFiberOver G p f) :
    (MorphismProperty.TrivialBundleWithFiberOver.mapFiber e h).t = h.t :=
  rfl

end MathlibExtTest.CategoryTheory.TrivialBundleWithFiberTransportTests
