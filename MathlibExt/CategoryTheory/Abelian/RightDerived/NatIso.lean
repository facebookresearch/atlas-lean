/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Copyright (c) 2026 @junekim623, Muse. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
Author: @toskua
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Right derivation of natural isomorphisms

The right-derived forward and inverse transformations form a natural
isomorphism. Additivity transfers through the specified functor
isomorphism, and the source requires injective resolutions.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.NatIso

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {F G : C ⥤ D} [F.Additive]

/-- Derive a natural isomorphism using the maps, earning target additivity. -/
def rightDerived (e : F ≅ G) (n : ℕ) :
    letI := Functor.additive_of_iso e
    F.rightDerived n ≅ G.rightDerived n := by
  letI := Functor.additive_of_iso e
  exact
    { hom := NatTrans.rightDerived e.hom n
      inv := NatTrans.rightDerived e.inv n
      hom_inv_id := by
        rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
      inv_hom_id := by
        rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id] }

@[simp]
theorem rightDerived_hom (e : F ≅ G) (n : ℕ) :
    letI := Functor.additive_of_iso e
    (rightDerived e n).hom = NatTrans.rightDerived e.hom n := rfl

@[simp]
theorem rightDerived_inv (e : F ≅ G) (n : ℕ) :
    letI := Functor.additive_of_iso e
    (rightDerived e n).inv = NatTrans.rightDerived e.inv n := rfl

/-- An functor square remains a square after right derivation. -/
@[reassoc]
theorem rightDerived_hom_naturality
    {F' G' : C ⥤ D} [F'.Additive]
    (e : F ≅ G) (e' : F' ≅ G') (f : F ⟶ F') (g : G ⟶ G')
    (w : f ≫ e'.hom = e.hom ≫ g) (n : ℕ) :
    letI := Functor.additive_of_iso e
    letI := Functor.additive_of_iso e'
    NatTrans.rightDerived f n ≫ (rightDerived e' n).hom =
      (rightDerived e n).hom ≫ NatTrans.rightDerived g n := by
  letI := Functor.additive_of_iso e
  letI := Functor.additive_of_iso e'
  change NatTrans.rightDerived f n ≫ NatTrans.rightDerived e'.hom n =
    NatTrans.rightDerived e.hom n ≫ NatTrans.rightDerived g n
  rw [← NatTrans.rightDerived_comp, w, NatTrans.rightDerived_comp]

@[simp]
theorem rightDerived_refl (F : C ⥤ D) [F.Additive] (n : ℕ) :
    rightDerived (Iso.refl F) n = Iso.refl (F.rightDerived n) := by
  apply Iso.ext
  exact NatTrans.rightDerived_id F n

@[simp]
theorem rightDerived_symm (e : F ≅ G) (n : ℕ) :
    letI := Functor.additive_of_iso e
    rightDerived e.symm n = (rightDerived e n).symm := by
  letI := Functor.additive_of_iso e
  apply Iso.ext
  rfl

@[simp]
theorem rightDerived_trans {H : C ⥤ D} (e : F ≅ G) (f : G ≅ H) (n : ℕ) :
    letI := Functor.additive_of_iso e
    letI := Functor.additive_of_iso f
    rightDerived (e ≪≫ f) n = rightDerived e n ≪≫ rightDerived f n := by
  letI := Functor.additive_of_iso e
  letI := Functor.additive_of_iso f
  apply Iso.ext
  exact NatTrans.rightDerived_comp e.hom f.hom n

end CategoryTheory.NatIso
