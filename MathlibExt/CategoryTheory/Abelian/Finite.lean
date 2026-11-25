/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Preadditive.Projective.Cover
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite linear abelian categories

Finiteness means finite-dimensional morphism spaces, finite length of each
object, finitely many simple isomorphism classes, and projective covers.
The native Artinian/Noetherian subobject conditions express finite length.
The native skeleton records isomorphism classes without requiring a finite
object type or finite morphism sets.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CategoryTheory

open Limits

universe w v u

/-- The full subcategory of simple objects. -/
abbrev SimpleObjects (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :=
  ObjectProperty.FullSubcategory (fun X : C => Simple X)

/-- The intrinsic finiteness conditions on an abelian linear category.
Projective covers retain essentiality, rather than only projective presentations. -/
class FiniteLinearCategory (k : Type w) (C : Type u) [Field k]
    [Category.{v} C] [Abelian C] [Linear k C] : Prop
    extends HasProjectiveCovers C where
  /-- Every morphism space is finite dimensional over the scalar field. -/
  homFinite : ∀ X Y : C, Module.Finite k (X ⟶ Y)
  /-- The ascending subobject chain condition on each object. -/
  noetherian : ∀ X : C, IsNoetherianObject X
  /-- The descending subobject chain condition on each object. -/
  artinian : ∀ X : C, IsArtinianObject X
  /-- Finitely many isomorphism classes of simple objects. -/
  finiteSimples : Finite (Skeleton (SimpleObjects C))

attribute [instance] FiniteLinearCategory.homFinite FiniteLinearCategory.noetherian
  FiniteLinearCategory.artinian FiniteLinearCategory.finiteSimples

end CategoryTheory
