/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.CategoryTheory.NatTrans.PointwiseArrow
public import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# Images of natural transformations in two indexing categories

Let B,I,C be categories, with images and image maps in C, and let α : F → G be a natural
transformation between functors B → (I → C). Taking the image of α_b(i) for each b and i gives
a functor B → (I → C).

Its maps are the canonical image maps of the squares supplied by α's naturality in the outer
and inner categories. The categories may have independent object and morphism universes.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace NatTrans

variable {B : Type u₁} [Category.{v₁} B]
variable {I : Type u₂} [Category.{v₂} I]
variable {C : Type u₃} [Category.{v₃} C]
variable [HasImages C] [HasImageMaps C]

/-- Let B,I,C be categories, assume C has images and image maps, and let α : F → G with F,G : B ⥤
I ⥤ C. Define a functor B ⥤ I ⥤ C whose object at (b,i) is image(α_b(i)). For a morphism in B
or I, use the canonical image map of the commutative square given by the corresponding
naturality of α. Thus the image objects are functorial in both indices. All three categories
may have independent object and morphism universes. -/
noncomputable def pointwiseImage {F G : B ⥤ I ⥤ C} (α : F ⟶ G) :
    B ⥤ I ⥤ C :=
  pointwiseArrow α ⋙
    (Functor.whiskeringRight I (Arrow C) C).obj (Limits.im (C := C))

@[simp]
lemma pointwiseImage_obj_obj {F G : B ⥤ I ⥤ C} (α : F ⟶ G) (b : B) (i : I) :
    ((pointwiseImage α).obj b).obj i = image ((α.app b).app i) :=
  rfl

@[simp]
lemma pointwiseImage_obj_map {F G : B ⥤ I ⥤ C} (α : F ⟶ G) (b : B)
    {i i' : I} (f : i ⟶ i') :
    ((pointwiseImage α).obj b).map f =
      image.map
        (Arrow.homMk ((F.obj b).map f) ((G.obj b).map f)
          ((α.app b).naturality f)) :=
  rfl

@[simp]
lemma pointwiseImage_map_app {F G : B ⥤ I ⥤ C} (α : F ⟶ G) {b b' : B}
    (f : b ⟶ b') (i : I) :
    ((pointwiseImage α).map f).app i =
      image.map
        (Arrow.homMk ((F.map f).app i) ((G.map f).app i)
          (congr_app (α.naturality f) i)) :=
  rfl

end NatTrans

end CategoryTheory
