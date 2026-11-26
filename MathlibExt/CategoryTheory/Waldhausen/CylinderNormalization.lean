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

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Normalization of a cylinder functor on zero-source arrows

Let C be a category with a zero object. The zero-arrow functor sends
A to the unique map 0 → A. For T:Arrow(C) → C, a target inclusion
back:Right → T and projection:T → Right, normalization consists of a
natural isomorphism T(0 → A) ≅ A whose forward map is the projection
and whose inverse is the target inclusion.

Consequently the projection T(0 → A) → A followed by the target inclusion
A → T(0 → A) is the identity of T(0 → A).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Waldhausen

variable {C : Type u} [Category.{v} C] [HasZeroObject C]

/-- For a category C with a zero object, the functor C → Arrow(C) sends
A to the unique map 0 → A and a morphism f:A → B to the square
with source side 1_0 and target side f. -/
noncomputable def zeroArrowFunctor : C ⥤ Arrow C where
  obj A := Arrow.mk ((isZero_zero C).to_ A)
  map {A B} f := Arrow.homMk (𝟙 (0 : C)) f
    (by apply (isZero_zero C).eq_of_src)
  map_id A := by
    apply Arrow.hom_ext
    · rfl
    · rfl
  map_comp f g := by
    apply Arrow.hom_ext
    · simp
    · rfl

/-- Let C have a zero object, T:Arrow(C) → C be a functor, and
back:Right → T, projection:T → Right natural transformations.
Cylinder normalization is a natural isomorphism T(0 → A) ≅ A
whose forward component is projection at 0 → A and whose inverse
is back at that arrow. -/
structure CylinderNormalization
    (T : Arrow C ⥤ C)
    (back : Arrow.rightFunc ⟶ T)
    (projection : T ⟶ Arrow.rightFunc) where
  zeroNormalization :
    zeroArrowFunctor ⋙ T ≅ 𝟭 C
  zeroNormalization_hom :
    zeroNormalization.hom =
      Functor.whiskerLeft zeroArrowFunctor projection
  zeroNormalization_inv :
    zeroNormalization.inv =
      Functor.whiskerLeft zeroArrowFunctor back

/-- For a category C with a zero object and normalized data
T:Arrow(C) → C, back:Right → T and projection:T → Right,
the composite T(0 → A) —projection→ A —back→ T(0 → A)
is the identity for every A. -/
theorem CylinderNormalization.projection_back
    {T : Arrow C ⥤ C}
    {back : Arrow.rightFunc ⟶ T}
    {projection : T ⟶ Arrow.rightFunc}
    (h : CylinderNormalization T back projection)
    (A : C) :
    projection.app (zeroArrowFunctor.obj A) ≫
      back.app (zeroArrowFunctor.obj A) =
        𝟙 (T.obj (zeroArrowFunctor.obj A)) := by
  have hcomp := h.zeroNormalization.hom_inv_id_app A
  rw [h.zeroNormalization_hom, h.zeroNormalization_inv] at hcomp
  exact hcomp

end CategoryTheory.Waldhausen

namespace CategoryTheory.Waldhausen

variable {C : Type u} [Category.{v} C] [HasZeroObject C]

private theorem zeroArrowFunctor_source_isZero_computed (X : C) :
    IsZero ((zeroArrowFunctor (C := C)).obj X).left := by
  change IsZero (0 : C)
  exact isZero_zero C

/-- In a category C with a zero object, the source object of the arrow
assigned to X by the zero-arrow functor is a zero object. -/
theorem zeroArrowFunctor_source_isZero (X : C) :
    IsZero ((zeroArrowFunctor (C := C)).obj X).left :=
  zeroArrowFunctor_source_isZero_computed X

attribute [inherit_doc CylinderNormalization] CylinderNormalization.zeroNormalization

end CategoryTheory.Waldhausen
