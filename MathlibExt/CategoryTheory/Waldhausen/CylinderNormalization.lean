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
# Zero-arrow normalization for Waldhausen cylinders

The minimal Waldhausen interface assumes a zero object but not a separate
`HasZeroMorphisms` structure.  The low-level `zeroArrowFunctor` therefore
uses the unique map from zero directly.

`CylinderNormalization` packages the source-faithful natural isomorphism
`T(0 ⟶ -) ≅ 𝟭 C`.  Its hom is the cylinder projection and its inverse is the
back inclusion.  The first consequence records the missing inverse identity
at zero arrows.

This file defines no full cylinder, cylinder axiom, Cyl-I exactness, Stage
cylinder, Approximation theorem, or K-theory consequence.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Waldhausen

variable {C : Type u} [Category.{v} C] [HasZeroObject C]

/-- The functor sending `A` to the unique arrow `0 ⟶ A`, requiring only a
zero object. -/
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

/-- Natural normalization of a cylinder functor on arrows over maps from
zero.  Projection and back inclusion are the two directions of the
normalization isomorphism. -/
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

/-- At a zero arrow, projection followed by back inclusion is the identity. -/
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

/-- The source of every original zero arrow is the actual selected zero object. -/
theorem zeroArrowFunctor_source_isZero (X : C) :
    IsZero ((zeroArrowFunctor (C := C)).obj X).left :=
  zeroArrowFunctor_source_isZero_computed X

attribute [inherit_doc CylinderNormalization] CylinderNormalization.zeroNormalization

end CategoryTheory.Waldhausen
