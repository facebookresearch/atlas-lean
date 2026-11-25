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

public import MathlibExt.CategoryTheory.DGSource.CochainBifunctor

/-!
# Zero morphisms under bicomplex prolongation

A bifunctor preserving zero morphisms in both variables induces a bicomplex
bifunctor preserving zero morphisms in the first variable. The construction
uses arbitrary complex shapes.
-/

@[expose] public section

open CategoryTheory Limits

universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [HasZeroMorphisms C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [HasZeroMorphisms C₂]
  {D : Type u₃} [Category.{v₃} D] [HasZeroMorphisms D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ X : C₁, (F.obj X).PreservesZeroMorphisms]
  {I₁ : Type w₁} {I₂ : Type w₂} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)

/-- Bicomplex prolongation sends a zero first-variable morphism to zero. -/
instance mapBifunctorHomologicalComplex_preservesZeroMorphisms :
    (F.mapBifunctorHomologicalComplex c₁ c₂).PreservesZeroMorphisms where
  map_zero K L := by
    apply NatTrans.ext
    funext Q
    apply HomologicalComplex.hom_ext
    intro i
    apply HomologicalComplex.hom_ext
    intro j
    change (F.map (0 : K.X i ⟶ L.X i)).app (Q.X j) = 0
    simp only [Functor.map_zero, CategoryTheory.Limits.zero_app]

end CategoryTheory.Functor
