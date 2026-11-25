/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor
public import MathlibExt.CategoryTheory.Functor.EquivalenceTransport

/-!
# Canonical zero-object representatives of arbitrary exact functors

An exact functor sends the selected source zero to a zero object, which need
not be the selected target zero. The canonical object replacement changes its
value at the selected source zero and transports every arrow through the
original unique zero isomorphism. The entire original functor is retained by
an explicit natural isomorphism.

The resulting functor is exact and sends the selected source zero literally
to the selected target zero. This is a construction for an arbitrary exact
functor. Its identity and composition comparisons include their whole arrow
formulas and the identity component after identifying the selected zeros.
No equality between independently selected zero objects is assumed.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

attribute [local instance] Classical.propDecidable

universe uC vC uD vD uE vE

namespace CategoryTheory.Functor.IsWaldhausenExact

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F G : C ⥤ D}

/-- A natural isomorphism transports all four fields of Waldhausen exactness. -/
theorem ofNatIso (hF : F.IsWaldhausenExact) (e : F ≅ G) : G.IsWaldhausenExact where
  map_isZero hX := (hF.map_isZero hX).of_iso (e.app _).symm
  map_cofibration f hf :=
    ((WaldhausenCategoryWithoutGluing.cofibrations (C := D)).arrow_mk_iso_iff
      (Arrow.isoMk (e.app _) (e.app _) (e.hom.naturality f).symm)).mp
        (hF.map_cofibration f hf)
  map_weakEquivalence f hf :=
    ((WaldhausenCategoryWithoutGluing.weakEquivalences (C := D)).arrow_mk_iso_iff
      (Arrow.isoMk (e.app _) (e.app _) (e.hom.naturality f).symm)).mp
        (hF.map_weakEquivalence f hf)
  map_pushout i f inl inr hi hP :=
    (hF.map_pushout i f inl inr hi hP).of_iso
      (e.app _) (e.app _) (e.app _) (e.app _)
      (e.hom.naturality f) (e.hom.naturality i)
      (e.hom.naturality inl) (e.hom.naturality inr)

private def replacementObject (F : C ⥤ D) (X : C) : D :=
  if X = (0 : C) then (0 : D) else F.obj X

private def replacementObjectIso (hF : F.IsWaldhausenExact) (X : C) :
    F.obj X ≅ replacementObject F X := by
  classical
  by_cases hX : X = (0 : C)
  · exact eqToIso (congrArg F.obj hX) ≪≫
      (hF.map_isZero (isZero_zero C)).isoZero ≪≫
      eqToIso (by simp only [replacementObject, ite_eq_left hX])
  · exact eqToIso (by simp only [replacementObject, ite_eq_right hX])

/-- Replace only the selected source-zero value, using the canonical whole
object-isomorphism replacement functor. -/
def zeroObjectReplacement (hF : F.IsWaldhausenExact) : C ⥤ D :=
  F.copyObj
    (show C → D from fun X => if X = (0 : C) then (0 : D) else F.obj X)
    (show (∀ X : C, F.obj X ≅ (if X = (0 : C) then (0 : D) else F.obj X)) from fun X => by
      classical
      by_cases hX : X = (0 : C)
      · exact eqToIso (congrArg F.obj hX) ≪≫
          (hF.map_isZero (isZero_zero C)).isoZero ≪≫
          eqToIso (by simp only [ite_eq_left hX])
      · exact eqToIso (by simp only [ite_eq_right hX]))

/-- The original exact functor and its representative are compared by the
canonical whole object-isomorphism replacement. -/
def zeroObjectReplacementIso (hF : F.IsWaldhausenExact) :
    F ≅ zeroObjectReplacement hF := by
  dsimp only [zeroObjectReplacement]
  exact F.isoCopyObj _ _

/-- The complete object family uses the selected target zero exactly at the
selected source zero and retains every other original object value. -/
theorem zeroObjectReplacement_obj (hF : F.IsWaldhausenExact) (X : C) :
    (zeroObjectReplacement hF).obj X =
      if X = (0 : C) then (0 : D) else F.obj X := rfl

/-- The representative maps the selected source zero to the selected target
zero by an earned literal equality. -/
theorem zeroObjectReplacement_obj_zero (hF : F.IsWaldhausenExact) :
    (zeroObjectReplacement hF).obj (0 : C) = (0 : D) := by
  classical
  simp [zeroObjectReplacement_obj]

/-- Every other original object value is retained. -/
theorem zeroObjectReplacement_obj_of_ne (hF : F.IsWaldhausenExact)
    {X : C} (hX : X ≠ (0 : C)) :
    (zeroObjectReplacement hF).obj X = F.obj X := by
  classical
  simp only [zeroObjectReplacement_obj, ite_eq_right hX]

private theorem replacementObjectIso_of_ne (hF : F.IsWaldhausenExact)
    {X : C} (hX : X ≠ (0 : C)) :
    replacementObjectIso hF X =
      eqToIso (zeroObjectReplacement_obj_of_ne hF hX).symm := by
  classical
  simp only [replacementObjectIso, dite_eq_right hX]
  rfl

/-- Every complete arrow is the original arrow conjugated by the actual
forward and inverse comparison components. -/
theorem zeroObjectReplacement_map (hF : F.IsWaldhausenExact)
    {X Y : C} (f : X ⟶ Y) :
    (zeroObjectReplacement hF).map f =
      (zeroObjectReplacementIso hF).inv.app X ≫ F.map f ≫
        (zeroObjectReplacementIso hF).hom.app Y := rfl

/-- The forward comparison at the selected zero is exactly the original
unique mapped-zero isomorphism after the earned target-object equality. -/
theorem zeroObjectReplacementIso_hom_zero (hF : F.IsWaldhausenExact) :
    (zeroObjectReplacementIso hF).hom.app (0 : C) ≫
        eqToHom (zeroObjectReplacement_obj_zero hF) =
      (hF.map_isZero (isZero_zero C)).isoZero.hom := by
  exact (hF.map_isZero (isZero_zero C)).eq_of_src _ _

/-- The inverse comparison at the selected zero retains the original
inverse of that same mapped-zero isomorphism. -/
theorem zeroObjectReplacementIso_inv_zero (hF : F.IsWaldhausenExact) :
    eqToHom (zeroObjectReplacement_obj_zero hF).symm ≫
        (zeroObjectReplacementIso hF).inv.app (0 : C) =
      (hF.map_isZero (isZero_zero C)).isoZero.inv := by
  exact (isZero_zero D).eq_of_src _ _

/-- All four exactness fields are derived from the original exact functor
and the canonical whole comparison. -/
theorem zeroObjectReplacement_isWaldhausenExact (hF : F.IsWaldhausenExact) :
    (zeroObjectReplacement hF).IsWaldhausenExact :=
  hF.ofNatIso (zeroObjectReplacementIso hF)

/-- If the original functor already sends the selected zero literally to
the selected zero, the entire representative is the same original functor. -/
theorem zeroObjectReplacement_eq_of_obj_zero (hF : F.IsWaldhausenExact)
    (h0 : F.obj (0 : C) = (0 : D)) : zeroObjectReplacement hF = F := by
  classical
  have hobj : ∀ X : C, F.obj X = (zeroObjectReplacement hF).obj X := by
    intro X
    by_cases hX : X = (0 : C)
    · subst X
      exact h0.trans (zeroObjectReplacement_obj_zero hF).symm
    · exact (zeroObjectReplacement_obj_of_ne hF hX).symm
  apply (Functor.ext_of_iso (zeroObjectReplacementIso hF) hobj ?_).symm
  intro X
  by_cases hX : X = (0 : C)
  · subst X
    exact (hF.map_isZero (isZero_zero C)).eq_of_src _ _
  · have hComponent : (zeroObjectReplacementIso hF).hom.app X =
        (replacementObjectIso hF X).hom := by rfl
    rw [hComponent]
    rw [replacementObjectIso_of_ne hF hX, eqToIso.hom]

/-- The representative of the original identity is the entire original identity. -/
theorem zeroObjectReplacement_id :
    zeroObjectReplacement (Functor.IsWaldhausenExact.id (C := C)) = 𝟭 C :=
  zeroObjectReplacement_eq_of_obj_zero (Functor.IsWaldhausenExact.id (C := C)) rfl

/-- The entire comparison for a functor already preserving the selected
zero is the identity after its earned functor equality. -/
theorem zeroObjectReplacementIso_hom_of_obj_zero (hF : F.IsWaldhausenExact)
    (h0 : F.obj (0 : C) = (0 : D)) (X : C) :
    (zeroObjectReplacementIso hF).hom.app X ≫
        eqToHom (Functor.congr_obj (zeroObjectReplacement_eq_of_obj_zero hF h0) X) =
      𝟙 (F.obj X) := by
  classical
  by_cases hX : X = (0 : C)
  · subst X
    exact (hF.map_isZero (isZero_zero C)).eq_of_src _ _
  · have hComponent : (zeroObjectReplacementIso hF).hom.app X =
        (replacementObjectIso hF X).hom := by rfl
    rw [hComponent]
    rw [replacementObjectIso_of_ne hF hX, eqToIso.hom, eqToHom_trans]
    exact eqToHom_refl _ _

/-- The original identity comparison is the identity on every complete
object after the literal representative equality. -/
theorem zeroObjectReplacementIso_hom_id (X : C) :
    (zeroObjectReplacementIso (Functor.IsWaldhausenExact.id (C := C))).hom.app X ≫
        eqToHom (Functor.congr_obj (zeroObjectReplacement_id (C := C)) X) = 𝟙 X :=
  zeroObjectReplacementIso_hom_of_obj_zero
    (Functor.IsWaldhausenExact.id (C := C)) rfl X

variable {E : Type uE} [Category.{vE} E] [HasZeroObject E] [WaldhausenCategoryWithoutGluing E]
variable {K : D ⥤ E}

/-- Source-first composition of the representatives is compared to the
representative of the original composite by the original complete comparison
isomorphisms, without identifying independently selected image zeros. -/
def zeroObjectReplacementCompIso (hF : F.IsWaldhausenExact) (hK : K.IsWaldhausenExact) :
    zeroObjectReplacement hF ⋙ zeroObjectReplacement hK ≅
      zeroObjectReplacement (hF.comp hK) :=
  Functor.isoWhiskerLeft (zeroObjectReplacement hF) (zeroObjectReplacementIso hK).symm ≪≫
    Functor.isoWhiskerRight (zeroObjectReplacementIso hF).symm K ≪≫
      zeroObjectReplacementIso (hF.comp hK)

/-- Every whole composition component retains the original inverse target
comparison, original image of the source inverse comparison, and original
forward composite comparison, in their actual order. -/
theorem zeroObjectReplacementCompIso_hom_app
    (hF : F.IsWaldhausenExact) (hK : K.IsWaldhausenExact) (X : C) :
    (zeroObjectReplacementCompIso hF hK).hom.app X =
      (zeroObjectReplacementIso hK).inv.app ((zeroObjectReplacement hF).obj X) ≫
        K.map ((zeroObjectReplacementIso hF).inv.app X) ≫
          (zeroObjectReplacementIso (hF.comp hK)).hom.app X := rfl

/-- The full inverse composition component has the reverse original order. -/
theorem zeroObjectReplacementCompIso_inv_app
    (hF : F.IsWaldhausenExact) (hK : K.IsWaldhausenExact) (X : C) :
    (zeroObjectReplacementCompIso hF hK).inv.app X =
      (zeroObjectReplacementIso (hF.comp hK)).inv.app X ≫
        K.map ((zeroObjectReplacementIso hF).hom.app X) ≫
          (zeroObjectReplacementIso hK).hom.app ((zeroObjectReplacement hF).obj X) := by
  simp only [zeroObjectReplacementCompIso, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app, Category.assoc]

/-- The actual composite of the representatives sends the selected source
zero to the selected final zero by the two produced object equalities. -/
theorem zeroObjectReplacement_comp_obj_zero
    (hF : F.IsWaldhausenExact) (hK : K.IsWaldhausenExact) :
    (zeroObjectReplacement hF ⋙ zeroObjectReplacement hK).obj (0 : C) = (0 : E) :=
  (congrArg (zeroObjectReplacement hK).obj (zeroObjectReplacement_obj_zero hF)).trans
    (zeroObjectReplacement_obj_zero hK)

/-- After the produced source and target zero identifications, the full
composition comparison has the actual identity zero component. -/
theorem zeroObjectReplacementCompIso_hom_zero
    (hF : F.IsWaldhausenExact) (hK : K.IsWaldhausenExact) :
    eqToHom (zeroObjectReplacement_comp_obj_zero hF hK).symm ≫
        (zeroObjectReplacementCompIso hF hK).hom.app (0 : C) ≫
          eqToHom (zeroObjectReplacement_obj_zero (hF.comp hK)) = 𝟙 (0 : E) := by
  exact (isZero_zero E).eq_of_src _ _

/-- The inverse composition comparison has the same actual identity zero component. -/
theorem zeroObjectReplacementCompIso_inv_zero
    (hF : F.IsWaldhausenExact) (hK : K.IsWaldhausenExact) :
    eqToHom (zeroObjectReplacement_obj_zero (hF.comp hK)).symm ≫
        (zeroObjectReplacementCompIso hF hK).inv.app (0 : C) ≫
          eqToHom (zeroObjectReplacement_comp_obj_zero hF hK) = 𝟙 (0 : E) := by
  exact (isZero_zero E).eq_of_src _ _

end CategoryTheory.Functor.IsWaldhausenExact

end
