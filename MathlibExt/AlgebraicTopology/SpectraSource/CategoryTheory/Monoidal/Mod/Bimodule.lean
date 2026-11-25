/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Monoidal/Mod/Bimodule.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Monoidal.Bimod

/-!
# Modules over a commutative monoid as bimodules

A left module over a commutative monoid object has a canonical right action,
obtained by moving the scalar past the module through the braiding. The two
actions commute, so this gives a native bimodule. Module maps respect both
actions. This adapter allows balanced tensor products of modules to use
Mathlib's `Bimod.TensorBimod` construction rather than a second coequalizer
construction.

The construction uses the inverse braiding from the scalar to the module;
in a symmetric monoidal category it is also the forward braiding in the
opposite order. No colimit or closedness assumptions are needed.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory MonoidalLeftAction MonObj BraidedCategory

namespace Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (A B : Mon C)

/-- Forget the right action of a bimodule, retaining its native left module. -/
-- Reducibility lets action and map equalities compare morphisms on the unchanged carrier.
abbrev toLeftMod : Bimod A B ⥤ Mod C A.X where
  obj M :=
    { X := M.X
      mod :=
        { smul := M.actLeft
          one_smul := M.one_actLeft
          mul_smul := M.left_assoc } }
  map f := Mod.Hom.mk' f.hom f.left_act_hom

@[simp]
theorem toLeftMod_obj_X (M : Bimod A B) : ((toLeftMod A B).obj M).X = M.X := (rfl)

/-- The left action is unchanged when forgetting the right action. -/
@[simp]
theorem toLeftMod_smul (M : Bimod A B) :
    ((toLeftMod A B).obj M).mod.smul = M.actLeft := (rfl)

end Bimod

namespace Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {A : C} [MonObj A] [IsCommMonObj A]

/-- Regard modules over a commutative monoid object as bimodules. The right
action moves the scalar to the left using the inverse braiding. -/
-- Reducibility lets action and map equalities compare morphisms on the unchanged carrier.
abbrev toBimod : Mod C A ⥤ Bimod (Mon.mk A) (Mon.mk A) where
  obj M :=
    { X := M.X
      actLeft := γ[A, M.X]
      one_actLeft := ModObj.one_smul_self A M.X
      left_assoc := ModObj.mul_smul_self A M.X
      actRight := (β_ A M.X).inv ≫ γ[A, M.X]
      actRight_one := by
        rw [braiding_inv_naturality_right_assoc, ModObj.one_smul_self]
        simp
      right_assoc := by
        simp only [Category.assoc, comp_whiskerRight]
        rw [braiding_inv_naturality_right_assoc,
          ModObj.mul_smul_self, braiding_inv_naturality_left_assoc]
        simp only [braiding_tensor_left_inv, braiding_tensor_right_inv, Category.assoc,
          Iso.hom_inv_id_assoc, ModObj.mul_smul_self_flip,
          ← comp_whiskerRight_assoc, IsCommMonObj.mul_comm']
      middle_assoc := by
        rw [braiding_inv_naturality_left_assoc, ModObj.mul_smul_self_flip]
        simp only [braiding_tensor_right_inv, Category.assoc, Iso.hom_inv_id_assoc,
          whiskerLeft_comp, ModObj.mul_smul_self_flip,
          ← comp_whiskerRight_assoc, IsCommMonObj.mul_comm'] }
  map f :=
    { hom := f.hom
      left_act_hom := IsModHom.smul_hom (f := f.hom)
      right_act_hom := by
        dsimp
        rw [Category.assoc, IsModHom.smul_hom]
        simp }

@[simp]
theorem toBimod_obj_X (M : Mod C A) : (toBimod.obj M).X = M.X := (rfl)

@[simp]
theorem toBimod_obj_actLeft (M : Mod C A) :
    (toBimod.obj M).actLeft = γ[A, M.X] := (rfl)

@[simp]
theorem toBimod_obj_actRight (M : Mod C A) :
    (toBimod.obj M).actRight = (β_ A M.X).inv ≫ γ[A, M.X] := (rfl)

@[simp]
theorem toBimod_map_hom {M N : Mod C A} (f : M ⟶ N) :
    (toBimod.map f).hom = f.hom := (rfl)

/-- A bimodule map between the canonical bimodules is determined by, and
uniquely lifts, a left-module map. -/
def fullyFaithfulToBimod : (toBimod (A := A)).FullyFaithful where
  preimage f := Hom.mk' f.hom f.left_act_hom
  map_preimage f := by ext; rfl
  preimage_map f := by ext; rfl

instance : (toBimod (A := A)).Full := fullyFaithfulToBimod.full

instance : (toBimod (A := A)).Faithful := fullyFaithfulToBimod.faithful

/-- Forgetting the added right action recovers the original module functorially. -/
def toBimodCompToLeftModIso :
    toBimod (A := A) ⋙ Bimod.toLeftMod (Mon.mk A) (Mon.mk A) ≅ 𝟭 (Mod C A) :=
  NatIso.ofComponents (fun M ↦
    { hom := Hom.mk' (𝟙 M.X) (IsModHom.smul_hom (A := A) (f := 𝟙 M.X))
      inv := Hom.mk' (𝟙 M.X) (IsModHom.smul_hom (A := A) (f := 𝟙 M.X))
      hom_inv_id := by ext; simp
      inv_hom_id := by ext; simp })
    (fun f ↦ by ext; simp)

@[simp]
theorem toBimodCompToLeftModIso_hom_app_hom (M : Mod C A) :
    (toBimodCompToLeftModIso.hom.app M).hom = 𝟙 M.X := (rfl)

@[simp]
theorem toBimodCompToLeftModIso_inv_app_hom (M : Mod C A) :
    (toBimodCompToLeftModIso.inv.app M).hom = 𝟙 M.X := (rfl)

/-- For the regular left module, the added right action is multiplication. -/
def toBimodRegularIso :
    toBimod.obj (Mod.regular A) ≅ Bimod.regular (Mon.mk A) := by
  dsimp [Mod.regular]
  exact Bimod.isoOfIso (Iso.refl A) (by
    dsimp [toBimod, Bimod.regular]
    simp) (by
    dsimp [toBimod, Bimod.regular]
    simp [IsCommMonObj.mul_comm'])

@[simp]
theorem toBimodRegularIso_hom_hom :
    toBimodRegularIso.hom.hom = eqToHom (Mod.regular_X A) := (rfl)

@[simp]
theorem toBimodRegularIso_inv_hom :
    toBimodRegularIso.inv.hom = eqToHom (Mod.regular_X A).symm := (rfl)

end Mod

namespace Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {A : C} [MonObj A] [IsCommMonObj A]

/-- A bimodule whose right action is induced from its left action is recovered
from that left module. Both comparison maps are the identity on the carrier. -/
def toLeftModToBimodIsoOfActRightEq (M : Bimod (Mon.mk A) (Mon.mk A))
    (h : M.actRight = (β_ A M.X).inv ≫ M.actLeft) :
    Mod.toBimod.obj ((toLeftMod (Mon.mk A) (Mon.mk A)).obj M) ≅ M :=
  Bimod.isoOfIso (Iso.refl M.X) (by
    simpa using toLeftMod_smul (Mon.mk A) (Mon.mk A) M) (by
    simpa [h] using toLeftMod_smul (Mon.mk A) (Mon.mk A) M)

@[simp]
theorem toLeftModToBimodIsoOfActRightEq_hom_hom (M : Bimod (Mon.mk A) (Mon.mk A))
    (h : M.actRight = (β_ A M.X).inv ≫ M.actLeft) :
    (toLeftModToBimodIsoOfActRightEq M h).hom.hom = 𝟙 M.X := (rfl)

@[simp]
theorem toLeftModToBimodIsoOfActRightEq_inv_hom (M : Bimod (Mon.mk A) (Mon.mk A))
    (h : M.actRight = (β_ A M.X).inv ≫ M.actLeft) :
    (toLeftModToBimodIsoOfActRightEq M h).inv.hom = 𝟙 M.X := (rfl)

end Bimod

end CategoryTheory
