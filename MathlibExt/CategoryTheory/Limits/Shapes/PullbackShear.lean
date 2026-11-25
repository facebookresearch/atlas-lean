/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Tactic.Abel

/-!
# Additive shears between pullbacks

If `a ≫ q = f - g`, the pullbacks along `f` and `g` are canonically
isomorphic. The first projection is fixed; the second subtracts `fst ≫ a`,
and the inverse adds it. Preadditivity and the two specified pullbacks
suffice.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe v u

namespace CategoryTheory.Limits.pullback

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X I Z : C} (q : I ⟶ Z) (f g : X ⟶ Z) (a : X ⟶ I)
  (ha : a ≫ q = f - g) [HasPullback f q] [HasPullback g q]

/-- The literal pullback shear, preserving the first projection. -/
def shearHom : pullback f q ⟶ pullback g q :=
  pullback.lift (pullback.fst f q)
    (pullback.snd f q - pullback.fst f q ≫ a) (by
      calc
        pullback.fst f q ≫ g =
            pullback.fst f q ≫ f - pullback.fst f q ≫ (f - g) := by
          rw [Preadditive.comp_sub]
          abel
        _ = pullback.snd f q ≫ q - (pullback.fst f q ≫ a) ≫ q := by
          rw [← pullback.condition, Category.assoc, ha]
        _ = (pullback.snd f q - pullback.fst f q ≫ a) ≫ q := by
          rw [Preadditive.sub_comp])

/-- The literal inverse shear, adding the same correction. -/
def shearInv : pullback g q ⟶ pullback f q :=
  pullback.lift (pullback.fst g q)
    (pullback.snd g q + pullback.fst g q ≫ a) (by
      calc
        pullback.fst g q ≫ f =
            pullback.fst g q ≫ g + pullback.fst g q ≫ (f - g) := by
          rw [Preadditive.comp_sub]
          abel
        _ = pullback.snd g q ≫ q + (pullback.fst g q ≫ a) ≫ q := by
          rw [← pullback.condition, Category.assoc, ha]
        _ = (pullback.snd g q + pullback.fst g q ≫ a) ≫ q := by
          rw [Preadditive.add_comp])

@[reassoc (attr := simp)]
theorem shearHom_fst : shearHom q f g a ha ≫ pullback.fst g q = pullback.fst f q := by
  simp [shearHom]

@[reassoc (attr := simp)]
theorem shearHom_snd :
    shearHom q f g a ha ≫ pullback.snd g q =
      pullback.snd f q - pullback.fst f q ≫ a := by
  simp [shearHom]

@[reassoc (attr := simp)]
theorem shearInv_fst : shearInv q f g a ha ≫ pullback.fst f q = pullback.fst g q := by
  simp [shearInv]

@[reassoc (attr := simp)]
theorem shearInv_snd :
    shearInv q f g a ha ≫ pullback.snd f q =
      pullback.snd g q + pullback.fst g q ≫ a := by
  simp [shearInv]

/-- Both inverse laws follow from the two projection equations. -/
theorem shearHom_comp_shearInv :
    shearHom q f g a ha ≫ shearInv q f g a ha = 𝟙 (pullback f q) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, shearInv_fst, shearHom_fst, Category.id_comp]
  · simp only [Category.assoc, shearInv_snd, Preadditive.comp_add,
      shearHom_snd, shearHom_fst_assoc, Category.id_comp, sub_add_cancel]

theorem shearInv_comp_shearHom :
    shearInv q f g a ha ≫ shearHom q f g a ha = 𝟙 (pullback g q) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, shearHom_fst, shearInv_fst, Category.id_comp]
  · simp only [Category.assoc, shearHom_snd, Preadditive.comp_sub,
      shearInv_snd, shearInv_fst_assoc, Category.id_comp, add_sub_cancel_right]

/-- The additive pullback shear isomorphism, with both explicit inverse maps. -/
def shearIso : pullback f q ≅ pullback g q where
  hom := shearHom q f g a ha
  inv := shearInv q f g a ha
  hom_inv_id := shearHom_comp_shearInv q f g a ha
  inv_hom_id := shearInv_comp_shearHom q f g a ha

end CategoryTheory.Limits.pullback
