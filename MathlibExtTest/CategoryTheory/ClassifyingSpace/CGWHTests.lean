/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.ClassifyingSpace.CGWH

/-!
# Tests for ordinary-category classifying spaces in CGWH
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe w v u

namespace MathlibExtTest.CategoryTheory.ClassifyingSpace.CGWHTests

#check CategoryTheory.classifyingSpaceCGWH
#check CategoryTheory.classifyingSpaceCGWHToTopIso

section Generic

variable {C D E : Type u}
variable [Category.{v} C] [Category.{v} D] [Category.{v} E]
variable (F : C ⥤ D) (G : D ⥤ E)

example : CategoryTheory.classifyingSpaceCGWH.{w, v, u}.obj (Cat.of C) =
    SSet.toCGWH.{w, max u v}.obj (CategoryTheory.nerve C) := rfl

example : CategoryTheory.classifyingSpaceCGWH.{w, v, u}.map F.toCatHom =
    SSet.toCGWH.{w, max u v}.map (CategoryTheory.nerveMap F) := rfl

example : CategoryTheory.classifyingSpaceCGWH.{w, v, u}.map
      (𝟙 (Cat.of C)) = 𝟙 _ :=
  CategoryTheory.classifyingSpaceCGWH.map_id (Cat.of C)

example : CategoryTheory.classifyingSpaceCGWH.{w, v, u}.map
      (F.toCatHom ≫ G.toCatHom) =
    CategoryTheory.classifyingSpaceCGWH.map F.toCatHom ≫
      CategoryTheory.classifyingSpaceCGWH.map G.toCatHom :=
  CategoryTheory.classifyingSpaceCGWH.map_comp F.toCatHom G.toCatHom

example :
    (CategoryTheory.classifyingSpaceCGWHToTopIso.{w, v, u}.app
      (Cat.of C)).hom = 𝟙 _ := rfl

example :
    (CategoryTheory.classifyingSpaceCGWHToTopIso.{w, v, u}.app
      (Cat.of C)).inv = 𝟙 _ := rfl

example :
    (CategoryTheory.classifyingSpaceCGWH.{w, v, u} ⋙
        CGWH.cgwhToTop.{w, max u v}).map F.toCatHom ≫
        (CategoryTheory.classifyingSpaceCGWHToTopIso.{w, v, u}.app
          (Cat.of D)).hom =
      (CategoryTheory.classifyingSpaceCGWHToTopIso.{w, v, u}.app
          (Cat.of C)).hom ≫
        (CategoryTheory.nerveFunctor.{v, u} ⋙
          SSet.toTop.{max u v}).map F.toCatHom :=
  CategoryTheory.classifyingSpaceCGWHToTopIso.{w, v, u}.hom.naturality
    F.toCatHom

example :
    (CategoryTheory.nerveFunctor.{v, u} ⋙
        SSet.toTop.{max u v}).map F.toCatHom ≫
        (CategoryTheory.classifyingSpaceCGWHToTopIso.{w, v, u}.app
          (Cat.of D)).inv =
      (CategoryTheory.classifyingSpaceCGWHToTopIso.{w, v, u}.app
          (Cat.of C)).inv ≫
        (CategoryTheory.classifyingSpaceCGWH.{w, v, u} ⋙
          CGWH.cgwhToTop.{w, max u v}).map F.toCatHom :=
  CategoryTheory.classifyingSpaceCGWHToTopIso.{w, v, u}.inv.naturality
    F.toCatHom

end Generic

section NonidentityMap

example : ((Functor.const (Type 0)).obj PUnit).obj Bool = PUnit := rfl

example : CategoryTheory.classifyingSpaceCGWH.{w, 0, 1}.map
      ((Functor.const (Type 0)).obj PUnit).toCatHom =
    SSet.toCGWH.{w, 1}.map
      (CategoryTheory.nerveMap
        ((Functor.const (Type 0)).obj PUnit)) := rfl

end NonidentityMap

section UniverseCorners

#check CategoryTheory.classifyingSpaceCGWH.{0, 0, 0}
#check CategoryTheory.classifyingSpaceCGWH.{1, 0, 0}
#check CategoryTheory.classifyingSpaceCGWH.{0, 1, 0}
#check CategoryTheory.classifyingSpaceCGWH.{0, 0, 1}
#check CategoryTheory.classifyingSpaceCGWHToTopIso.{0, 1, 0}
#check CategoryTheory.classifyingSpaceCGWHToTopIso.{1, 0, 1}

end UniverseCorners

#print axioms CategoryTheory.classifyingSpaceCGWH
#print axioms CategoryTheory.classifyingSpaceCGWHToTopIso

/- No pointed, model, weak-equivalence, bar, or spectra facade is added. -/

/-- error: Unknown identifier `CategoryTheory.BC` -/
#guard_msgs (error) in
#check CategoryTheory.BC

/-- error: Unknown constant `CGWH.classifyingSpace` -/
#guard_msgs (error) in
#check CGWH.classifyingSpace

/-- error: Unknown identifier `PointedCGWH` -/
#guard_msgs (error) in
#check PointedCGWH

/-- error: Unknown identifier `CategoryTheory.classifyingSpaceCGWHWeakEquivalence` -/
#guard_msgs (error) in
#check CategoryTheory.classifyingSpaceCGWHWeakEquivalence

end MathlibExtTest.CategoryTheory.ClassifyingSpace.CGWHTests
