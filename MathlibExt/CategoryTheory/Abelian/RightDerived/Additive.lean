/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Additivity of injective resolutions and right-derived functors

The functor `injectiveResolutions C`, sending an object to (a choice of) its
injective resolution in the homotopy category, is additive. As a consequence,
the right-derived functors `F.rightDerived n` of an additive functor `F` are
additive.

Dual of `MathlibExt.CategoryTheory.Abelian.LeftDerived.Additive`
(Adam Kiezun), with the same structure and dualized proof.
-/

@[expose] public section

namespace CategoryTheory

open Category

universe v u

section

variable (C : Type u) [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]

/-- The functor sending an object to a choice of injective resolution is
additive: the descent of a sum of morphisms is homotopic to the sum of the
descents. -/
instance injectiveResolutions_additive :
    Functor.Additive (injectiveResolutions C) where
  map_add {X Y f g} := by
    dsimp [injectiveResolutions]
    suffices h : (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc (f + g) (injectiveResolution Y)
          (injectiveResolution X)) =
      (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X) +
         InjectiveResolution.desc g (injectiveResolution Y) (injectiveResolution X)) by
      rw [h]
      exact (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map_add
    apply HomotopyCategory.eq_of_homotopy
    apply InjectiveResolution.descHomotopy (f + g)
    · exact InjectiveResolution.desc_commutes (f + g) _ _
    · rw [Preadditive.comp_add, InjectiveResolution.desc_commutes f,
          InjectiveResolution.desc_commutes g,
          ← Preadditive.add_comp, ← Functor.map_add]

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type*} [Category* D] [Abelian D]

/-- The right-derived functors of an additive functor are additive. -/
instance rightDerived_additive (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.rightDerived n).Additive := by
  dsimp only [Functor.rightDerived, Functor.rightDerivedToHomotopyCategory]
  infer_instance

end

end CategoryTheory
