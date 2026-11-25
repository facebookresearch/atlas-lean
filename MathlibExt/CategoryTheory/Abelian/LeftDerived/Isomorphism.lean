/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Abelian.LeftDerived

/-!
# Left derivation of natural isomorphisms

Deriving the forward and inverse transformations gives a natural
isomorphism of left-derived functors. Additivity transfers through the
specified isomorphism; finite-colimit preservation is unnecessary.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory

universe u₁ v₁ u₂ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasProjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {F G : C ⥤ D} [F.Additive]

/-- Left derivation carries an natural isomorphism to an isomorphism. -/
def NatIso.leftDerived (e : F ≅ G) (n : ℕ) :
    letI := Functor.additive_of_iso e
    F.leftDerived n ≅ G.leftDerived n := by
  letI := Functor.additive_of_iso e
  exact
    { hom := NatTrans.leftDerived e.hom n
      inv := NatTrans.leftDerived e.inv n
      hom_inv_id := by
        rw [← NatTrans.leftDerived_comp, e.hom_inv_id, NatTrans.leftDerived_id]
      inv_hom_id := by
        rw [← NatTrans.leftDerived_comp, e.inv_hom_id, NatTrans.leftDerived_id] }

/-- Its forward map is the derived transformation. -/
@[simp]
theorem NatIso.leftDerived_hom (e : F ≅ G) (n : ℕ) :
    letI := Functor.additive_of_iso e
    (NatIso.leftDerived e n).hom = NatTrans.leftDerived e.hom n := rfl

/-- Its inverse is the derived inverse transformation. -/
@[simp]
theorem NatIso.leftDerived_inv (e : F ≅ G) (n : ℕ) :
    letI := Functor.additive_of_iso e
    (NatIso.leftDerived e n).inv = NatTrans.leftDerived e.inv n := rfl

/-- An square of functor maps commutes after left derivation.
Additivity of the two target functors is from the supplied isomorphisms. -/
@[reassoc]
theorem NatIso.leftDerived_hom_naturality
    {F' G' : C ⥤ D} [F'.Additive]
    (e : F ≅ G) (e' : F' ≅ G') (f : F ⟶ F') (g : G ⟶ G')
    (w : f ≫ e'.hom = e.hom ≫ g) (n : ℕ) :
    letI := Functor.additive_of_iso e
    letI := Functor.additive_of_iso e'
    NatTrans.leftDerived f n ≫ (NatIso.leftDerived e' n).hom =
      (NatIso.leftDerived e n).hom ≫ NatTrans.leftDerived g n := by
  letI := Functor.additive_of_iso e
  letI := Functor.additive_of_iso e'
  change NatTrans.leftDerived f n ≫ NatTrans.leftDerived e'.hom n =
    NatTrans.leftDerived e.hom n ≫ NatTrans.leftDerived g n
  rw [← NatTrans.leftDerived_comp, w, NatTrans.leftDerived_comp]

/-- Left derivation retains the identity isomorphism. -/
@[simp]
theorem NatIso.leftDerived_refl (n : ℕ) :
    NatIso.leftDerived (Iso.refl F) n = Iso.refl (F.leftDerived n) := by
  apply Iso.ext
  exact NatTrans.leftDerived_id F n

/-- Deriving the inverse is the inverse of the derived isomorphism. -/
@[simp]
theorem NatIso.leftDerived_symm (e : F ≅ G) (n : ℕ) :
    letI := Functor.additive_of_iso e
    NatIso.leftDerived e.symm n = (NatIso.leftDerived e n).symm := rfl

/-- Left derivation preserves isomorphism composition. -/
@[simp]
theorem NatIso.leftDerived_trans {H : C ⥤ D} (e : F ≅ G) (e' : G ≅ H) (n : ℕ) :
    letI := Functor.additive_of_iso e
    letI := Functor.additive_of_iso e'
    NatIso.leftDerived (e ≪≫ e') n = NatIso.leftDerived e n ≪≫ NatIso.leftDerived e' n := by
  let := Functor.additive_of_iso e
  let := Functor.additive_of_iso e'
  apply Iso.ext
  exact NatTrans.leftDerived_comp e.hom e'.hom n

end CategoryTheory

end
