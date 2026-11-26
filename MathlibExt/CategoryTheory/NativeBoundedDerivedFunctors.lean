/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeBoundedBimoduleModels

/-!
# Native restriction of fixed derived functors to actual bounded objects

Boundedness is an explicit source proof about each original native
derived functor and its actual homology. The restricted functor retains
all original objects/maps. Source: Mathlib56a005 native full subcategory,
Apache2.0; DK1311.2374v2 Sections2.2,3.3,4.10.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeBoundedDerivedFunctors

open _root_.CategoryTheory NativeBoundedBimoduleModels

universe uA uB vA vB
variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
attribute [local instance] HasDerivedCategory.standard

variable (F : DerivedCategory A ⥤ DerivedCategory B)

structure BoundedFunctorSource : Prop where
  bounded : ∀ K : (IsBoundedDerived A).FullSubcategory, IsBoundedDerived B (F.obj K.obj)

def boundedFunctor (S : BoundedFunctorSource F) :
    (IsBoundedDerived A).FullSubcategory ⥤ (IsBoundedDerived B).FullSubcategory where
  obj K := ⟨F.obj K.obj, S.bounded K⟩
  map f := ObjectProperty.homMk (F.map f.hom)
  map_id K := by apply ObjectProperty.hom_ext; exact F.map_id K.obj
  map_comp f g := by apply ObjectProperty.hom_ext; exact F.map_comp f.hom g.hom

end MathlibExt.CategoryTheory.NativeBoundedDerivedFunctors
