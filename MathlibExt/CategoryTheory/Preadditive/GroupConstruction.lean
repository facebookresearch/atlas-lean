/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Group.CommutativeOfDoubling
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Preadditivity from actual Hom groups and composition group maps

The input data are the original groups, their proved commuting law and
both actual composition group maps. Their full underlying functions are
specified. The constructed additive structure retains those operations
and the original category carrier and composition.
-/

@[expose] public section

noncomputable section

universe u v

namespace CategoryTheory.Preadditive

variable {C : Type u} [Category.{v} C]

/-- Actual commutative Hom groups and the two original composition functions construct preadditivity. -/
@[instance_reducible]
def ofHomGroups
    (G : ∀ X Y : C, Group (X ⟶ Y))
    (hc : ∀ X Y : C, letI := G X Y; ∀ f h : X ⟶ Y, f * h = h * f)
    (post : ∀ (X Y Z : C) (_h : Y ⟶ Z), letI := G X Y; letI := G X Z; (X ⟶ Y) →* (X ⟶ Z))
    (hp : ∀ (X Y Z : C) (h : Y ⟶ Z) (f : X ⟶ Y), post X Y Z h f = f ≫ h)
    (pre : ∀ (X Y Z : C) (_f : X ⟶ Y), letI := G Y Z; letI := G X Z; (Y ⟶ Z) →* (X ⟶ Z))
    (hf : ∀ (X Y Z : C) (f : X ⟶ Y) (h : Y ⟶ Z), pre X Y Z f h = f ≫ h) : Preadditive C where
  homGroup X Y := @Additive.addCommGroup _ (GroupDoubling.commGroup (G X Y) (hc X Y))
  add_comp := by
    intro X Y Z f f' h
    let (U V : C) : Group (U ⟶ V) := G U V
    change (f * f') ≫ h = (f ≫ h) * (f' ≫ h)
    exact (hp X Y Z h (f * f')).symm.trans
      (((post X Y Z h).map_mul f f').trans (congrArg₂ (· * ·) (hp X Y Z h f) (hp X Y Z h f')))
  comp_add := by
    intro X Y Z f h h'
    let (U V : C) : Group (U ⟶ V) := G U V
    change f ≫ (h * h') = (f ≫ h) * (f ≫ h')
    exact (hf X Y Z f (h * h')).symm.trans
      (((pre X Y Z f).map_mul h h').trans (congrArg₂ (· * ·) (hf X Y Z f h) (hf X Y Z f h')))

end CategoryTheory.Preadditive
