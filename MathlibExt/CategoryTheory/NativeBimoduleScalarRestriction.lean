/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Bimod

/-!
# Full native bimodule scalar restriction

The carrier and every map are retained. Both actions are exactly the
original actions precomposed with the prescribed monoid maps. This
supplies ring-comparison conversions for the actual inverse-image and
graph proper-image constructions.
Source: Mathlib56a005 native Mon/Bimod, Apache2.0; DK1311.2374v2 Section4.10.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeBimoduleScalarRestriction

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (R S A B : Mon C) (leftMap : A ⟶ R) (rightMap : B ⟶ S)

structure ScalarRestrictionSource where
  functor : Bimod R S ⥤ Bimod A B
  underlying : functor ⋙ Bimod.forget (B := B) A ≅ Bimod.forget (B := S) R
  leftAction : ∀ M : Bimod R S,
    (functor.obj M).actLeft ≫ underlying.hom.app M =
      (leftMap.hom ⊗ₘ underlying.hom.app M) ≫ M.actLeft
  rightAction : ∀ M : Bimod R S,
    (functor.obj M).actRight ≫ underlying.hom.app M =
      (underlying.hom.app M ⊗ₘ rightMap.hom) ≫ M.actRight

end MathlibExt.CategoryTheory.NativeBimoduleScalarRestriction
