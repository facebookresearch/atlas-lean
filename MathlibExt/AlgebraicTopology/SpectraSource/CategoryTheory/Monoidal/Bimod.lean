/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Monoidal/Bimod.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.CategoryTheory.Monoidal.Bimod
public import Mathlib.CategoryTheory.Bicategory.End

/-!
# The monoidal category of bimodules over a monoid object

Let `R` be a monoid object in a monoidal category `C` with coequalizers, such that tensoring on
either side preserves (universe-`0` small) colimits. Mathlib's bicategory `Bimod.monBicategory`
of monoids and bimodules makes the category `Bimod R R` of endomorphisms of `R` a monoidal
category, under the tensor product of bimodules `Bimod.tensorBimod`. This file records that
instance and describes its structure maps on representatives in the tensor products of the
underlying objects.

## Main definitions

* `Bimod.monoidalCategory`: the monoidal category of `R`-`R`-bimodules under the tensor product of
  bimodules.

## Main statements

* `Bimod.π_whiskerLeft_hom`, `Bimod.π_whiskerRight_hom`, `Bimod.π_associator_hom_hom`,
  `Bimod.π_leftUnitor_hom_hom` and `Bimod.π_rightUnitor_hom_hom`: the monoidal structure on
  representatives.
* `Bimod.tensorBimod_actRight_eq`: in a braided category, the tensor product of bimodules whose
  right actions are their left actions moved through the braiding again has this property.
-/

public section

universe v u

open CategoryTheory MonoidalCategory BraidedCategory Limits

namespace Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] {R : Mon C}

/-- Bimodules over a monoid object `R` form a monoidal category under the tensor product of
bimodules, with unit the regular bimodule: the category of endomorphisms of `R` in Mathlib's
bicategory `Bimod.monBicategory`. -/
noncomputable instance monoidalCategory (R : Mon C) : MonoidalCategory (Bimod R R) :=
  @instMonoidalCategoryHom _ monBicategory R

/-- Whiskering on the left acts on representatives in `P.X ⊗ Q.X` by whiskering on the left. -/
@[reassoc]
theorem π_whiskerLeft_hom (P : Bimod R R) {Q Q' : Bimod R R} (g : Q ⟶ Q') :
    coequalizer.π (P.actRight ▷ Q.X) ((α_ P.X R.X Q.X).hom ≫ P.X ◁ Q.actLeft) ≫ (P ◁ g).hom =
      P.X ◁ g.hom ≫
        coequalizer.π (P.actRight ▷ Q'.X) ((α_ P.X R.X Q'.X).hom ≫ P.X ◁ Q'.actLeft) :=
  ι_colimMap _ _

/-- Whiskering on the right acts on representatives in `P.X ⊗ Q.X` by whiskering on the right. -/
@[reassoc]
theorem π_whiskerRight_hom {P P' : Bimod R R} (f : P ⟶ P') (Q : Bimod R R) :
    coequalizer.π (P.actRight ▷ Q.X) ((α_ P.X R.X Q.X).hom ≫ P.X ◁ Q.actLeft) ≫ (f ▷ Q).hom =
      f.hom ▷ Q.X ≫
        coequalizer.π (P'.actRight ▷ Q.X) ((α_ P'.X R.X Q.X).hom ≫ P'.X ◁ Q.actLeft) :=
  ι_colimMap _ _

/-- The associator of bimodules on representatives in `P.X ⊗ Q.X ⊗ L.X` is the associator of the
underlying objects. -/
@[reassoc]
theorem π_associator_hom_hom (P Q L : Bimod R R) :
    coequalizer.π (P.actRight ▷ Q.X) ((α_ P.X R.X Q.X).hom ≫ P.X ◁ Q.actLeft) ▷ L.X ≫
        coequalizer.π ((P ⊗ Q).actRight ▷ L.X)
          ((α_ (P ⊗ Q).X R.X L.X).hom ≫ (P ⊗ Q).X ◁ L.actLeft) ≫ (α_ P Q L).hom.hom =
      (α_ P.X Q.X L.X).hom ≫
        P.X ◁ coequalizer.π (Q.actRight ▷ L.X) ((α_ Q.X R.X L.X).hom ≫ Q.X ◁ L.actLeft) ≫
          coequalizer.π (P.actRight ▷ (Q ⊗ L).X)
            ((α_ P.X R.X (Q ⊗ L).X).hom ≫ P.X ◁ (Q ⊗ L).actLeft) := by
  -- The associator is Mathlib's `AssociatorBimod.hom`, which descends twice along these
  -- coequalizers.
  change _ ≫ _ ≫ AssociatorBimod.hom P Q L = _
  rw [AssociatorBimod.hom, coequalizer.π_desc]
  apply π_tensor_id_preserves_coequalizer_inv_desc

/-- The left unitor of bimodules is induced by the left action. -/
@[reassoc]
theorem π_leftUnitor_hom_hom (P : Bimod R R) :
    coequalizer.π ((regular R).actRight ▷ P.X)
        ((α_ (regular R).X R.X P.X).hom ≫ (regular R).X ◁ P.actLeft) ≫ (λ_ P).hom.hom =
      P.actLeft :=
  coequalizer.π_desc _ _

/-- The right unitor of bimodules is induced by the right action. -/
@[reassoc]
theorem π_rightUnitor_hom_hom (P : Bimod R R) :
    coequalizer.π (P.actRight ▷ (regular R).X)
        ((α_ P.X R.X (regular R).X).hom ≫ P.X ◁ (regular R).actLeft) ≫ (ρ_ P).hom.hom =
      P.actRight :=
  coequalizer.π_desc _ _

variable [BraidedCategory C] in
/-- If the right actions of two `R`-`R`-bimodules are their left actions precomposed with the
inverse braiding, then so is the right action of their tensor product. -/
theorem tensorBimod_actRight_eq (P Q : Bimod R R)
    (hP : P.actRight = (β_ R.X P.X).inv ≫ P.actLeft)
    (hQ : Q.actRight = (β_ R.X Q.X).inv ≫ Q.actLeft) :
    (P.tensorBimod Q).actRight = (β_ R.X _).inv ≫ (P.tensorBimod Q).actLeft := by
  refine (cancel_epi ((tensorRight R.X).map (coequalizer.π _ _))).1 ?_
  dsimp
  rw [TensorBimod.π_tensor_id_actRight]
  dsimp only [TensorBimod.X]
  rw [braiding_inv_naturality_left_assoc,
    TensorBimod.whiskerLeft_π_actLeft, hQ, braiding_tensor_right_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc, ← hP]
  rw [coequalizer.condition]
  simp

end Bimod
