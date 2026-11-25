/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.OneSided

/-!
# The original regular bimodule as a free one-sided module

Both one-sided regular modules are the original free module on the base
tensor unit. The isomorphisms use the actual free adjunctions, monoid unit
and multiplication, and the original left and right unitors. No cofibrancy
of the regular bimodule over the paired scalar is asserted.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory MonoidalCategory MonoidalOpposite MonObj
open scoped MonoidalCategory

namespace Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

/-- The actual free left module on the base unit is the original one-sided regular module. -/
def regularLeftFreeIso (A : Mon C) :
    (Mod.free A.X).obj (𝟙_ C) ≅ toLeftModule (regular A) := by
  let F := (Mod.free A.X).obj (𝟙_ C)
  let N := toLeftModule (regular A)
  let e : F.X ≅ N.X := ρ_ A.X
  let f : F ⟶ N := ((Mod.freeForgetAdjunction A.X).homEquiv (𝟙_ C) N).symm η[A.X]
  have hf : f.hom = e.hom := by
    rw [Mod.freeForgetAdjunction_homEquiv_symm_apply_hom]
    change 𝟙 (A.X ⊗ (𝟙_ C)) ≫ (A.X ◁ η[A.X]) ≫ μ[A.X] = (ρ_ A.X).hom
    rw [Category.id_comp, MonObj.mul_one]
  letI : ModObj A.X F.X := F.mod
  letI : ModObj A.X N.X := N.mod
  letI : IsModHom A.X e.hom := by
    rw [← hf]
    exact f.isModHom
  exact
    { hom := ⟨e.hom⟩
      inv := ⟨e.inv⟩
      hom_inv_id := by apply Mod.hom_ext; exact e.hom_inv_id
      inv_hom_id := by apply Mod.hom_ext; exact e.inv_hom_id }

/-- The whole original left regular comparison is its right unitor. -/
theorem regularLeftFreeIso_hom (A : Mon C) :
    (regularLeftFreeIso A).hom.hom = (ρ_ A.X).hom := rfl

/-- The actual free right module on the base unit is the other original one-sided regular module. -/
def regularRightFreeIso (A : Mon C) :
    RightModuleFree.freeObject A.X (𝟙_ C) ≅ toRightModule (regular A) := by
  let F := RightModuleFree.freeObject A.X (𝟙_ C)
  let N := toRightModule (regular A)
  let e : F.X ≅ N.X := λ_ A.X
  let f : F ⟶ N := RightModuleFree.extendFree A.X (𝟙_ C) N η[A.X]
  have hf : f.hom = e.hom := by
    have h := congrFun (RightModuleFree.extendFree_hom A.X (𝟙_ C) N) η[A.X]
    change f.hom = (η[A.X] ▷ A.X) ≫ μ[A.X] at h
    exact h.trans (MonObj.one_mul A.X)
  letI : ModObj (mop A.X) F.X := F.mod
  letI : ModObj (mop A.X) N.X := N.mod
  letI : IsModHom (mop A.X) e.hom := by
    rw [← hf]
    exact f.isModHom
  exact
    { hom := ⟨e.hom⟩
      inv := ⟨e.inv⟩
      hom_inv_id := by apply Mod.hom_ext; exact e.hom_inv_id
      inv_hom_id := by apply Mod.hom_ext; exact e.inv_hom_id }

/-- The whole original right regular comparison is its left unitor. -/
theorem regularRightFreeIso_hom (A : Mon C) :
    (regularRightFreeIso A).hom.hom = (λ_ A.X).hom := rfl

end Bimod
