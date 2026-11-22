/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Transport of module structures along isomorphisms

For a monoid object A in a monoidal category, an isomorphism from a left A-module carrier
H.X to G transports the action to G by conjugation. The transported module is isomorphic to
H, and the underlying maps of the module isomorphism are exactly the supplied isomorphism
and its inverse.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace NativeOmegaRecovery.ModuleIsoTransport
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (A : C) [MonObj A]

/-- The existing lawful module transport moves only the actual original
module across its given underlying iso. -/
def object (H : Mod C A) {G : C} (e : H.X ≅ G) : Mod C A := by
  letI : ModObj A H.X := H.mod
  letI : IsMonHom (Iso.refl A).hom := by
    change IsMonHom (𝟙 A)
    infer_instance
  exact { X := G, mod := ModObj.ofIso (Iso.refl A) e }

/-- The existing transported action is the original full action conjugated by
that actual underlying iso. -/
theorem smul (H : Mod C A) {G : C} (e : H.X ≅ G) :
    (object A H e).mod.smul = (A ◁ e.inv) ≫ H.mod.smul ≫ e.hom := by
  let : ModObj A H.X := H.mod
  let : IsMonHom (Iso.refl A).hom := by
    change IsMonHom (𝟙 A)
    infer_instance
  change (𝟙 A ⊗ₘ e.inv) ≫ H.mod.smul ≫ e.hom = _
  rw [id_tensorHom]

/-- Both given underlying maps are actual inverse module maps; their linearity
comes from the original module and existing lawful transport. -/
def iso (H : Mod C A) {G : C} (e : H.X ≅ G) : H ≅ object A H e := by
  let K := object A H e
  letI : ModObj A H.X := H.mod
  letI : ModObj A G := K.mod
  let s : A ⊗ G ⟶ G := K.mod.smul
  have hs : s = (A ◁ e.inv) ≫ H.mod.smul ≫ e.hom := smul A H e
  have hid : (A ◁ e.hom) ≫ (A ◁ e.inv) = 𝟙 (A ⊗ H.X) :=
    (whiskerLeft_comp A e.hom e.inv).symm.trans
      ((congrArg (fun z : H.X ⟶ H.X => A ◁ z) e.hom_inv_id).trans
        (whiskerLeft_id A H.X))
  have h : H.mod.smul ≫ e.hom = (A ◁ e.hom) ≫ s := by
    rw [hs, ← Category.assoc, hid, Category.id_comp]
  letI : IsModHom A e.hom := ⟨h⟩
  have hi : K.mod.smul ≫ e.inv = (A ◁ e.inv) ≫ H.mod.smul :=
    IsModHom.smul_hom (A := A) (f := e.inv)
  exact
    { hom := Mod.Hom.mk' e.hom h
      inv := Mod.Hom.mk' e.inv hi
      hom_inv_id := by apply Mod.hom_ext; exact e.hom_inv_id
      inv_hom_id := by apply Mod.hom_ext; exact e.inv_hom_id }

/-- The full transported module forward map is the actual underlying forward map. -/
theorem iso_hom (H : Mod C A) {G : C} (e : H.X ≅ G) :
    (iso A H e).hom.hom = e.hom := rfl

/-- The full transported inverse is the same actual underlying inverse map. -/
theorem iso_inv (H : Mod C A) {G : C} (e : H.X ≅ G) :
    (iso A H e).inv.hom = e.inv := rfl

end NativeOmegaRecovery.ModuleIsoTransport
