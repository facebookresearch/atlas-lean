/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.CategoryTheory.Core
public import MathlibExt.CategoryTheory.Limits.Shapes.BiproductFunctor

/-!
# Left biproduct translation on the core

For a category with chosen binary biproducts, fixing an object `A` in the
left input of `biprodFunctor` gives the endofunctor `A ⊞ -`.  Restricting this
functor with `Functor.core` gives a neutral endofunctor of `Core C`: objects
are sent to `A ⊞ X.of`, and an isomorphism `g` is sent to
`biprod.map (𝟙 A) g.iso.hom` on forward maps.

The construction deliberately reuses the existing functors, so identity and
composition laws are inherited rather than reproved.  This file contains no
S⁻¹S-, Quillen-Q-, localization-, action-, or coherence-specific structure.
In particular, translation by a zero object is not claimed to be literally
the identity functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasBinaryBiproducts C]

/-- Left biproduct translation on the core, sending `X` to `A ⊞ X`. -/
noncomputable def coreLeftBiprodFunctor (A : C) : Core C ⥤ Core C :=
  (((Functor.const C).obj A).prod' (𝟭 C) ⋙ biprodFunctor C).core

/-- The underlying object of a core left-biproduct translate is the chosen
biproduct `A ⊞ X.of`. -/
@[simp]
theorem coreLeftBiprodFunctor_obj_of (A : C) (X : Core C) :
    ((coreLeftBiprodFunctor A).obj X).of = (A ⊞ X.of : C) :=
  rfl

/-- The forward map of a translated core isomorphism is the corresponding
biproduct map. -/
@[simp]
theorem coreLeftBiprodFunctor_map_iso_hom
    (A : C) {X Y : Core C} (g : X ⟶ Y) :
    ((coreLeftBiprodFunctor A).map g).iso.hom =
      biprod.map (𝟙 A) g.iso.hom :=
  rfl

end CategoryTheory.Limits

end
