/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule

/-!
# Preimages of submodules of sheaves of modules

Pulling back a submodule along a morphism uses the stock pointwise
`Submodule.comap`. Naturality preserves restriction stability, and its
membership sieve is the membership sieve of the actual image section.
Consequently a sheaf submodule has a sheaf submodule as its preimage.
The induced map to the original submodule has the literal inclusion triangle.
-/

@[expose] public section
noncomputable section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M P : PresheafOfModules.{v} R}

/-- The pointwise preimage of a presheaf submodule, with restriction
stability earned from the actual morphism's naturality. -/
def comap (N : P.Submodule) (f : M ⟶ P) : M.Submodule where
  obj X := (N.obj X).comap (f.app X).hom
  map {X Y} g := by
    intro x hx
    change (f.app Y) (M.map g x) ∈ N.obj Y
    rw [PresheafOfModules.naturality_apply]
    exact N.map_mem g hx

/-- The preimage has exactly the stock pointwise linear-map preimage. -/
theorem comap_obj (N : P.Submodule) (f : M ⟶ P) (X : Cᵒᵖ) :
    (N.comap f).obj X = (N.obj X).comap (f.app X).hom := rfl

/-- Local preimage membership is exactly local membership of the actual
image section, through the original morphism and restriction maps. -/
theorem comap_sieveOfSection (N : P.Submodule) (f : M ⟶ P) {X : Cᵒᵖ} (x : M.obj X) :
    (N.comap f).toSubfunctor.sieveOfSection x =
      N.toSubfunctor.sieveOfSection ((f.app X) x) := by
  ext Y g
  change ((f.app (Opposite.op Y)) (M.map g.op x) ∈ N.obj (Opposite.op Y)) ↔
    (P.map g.op ((f.app X) x) ∈ N.obj (Opposite.op Y))
  rw [PresheafOfModules.naturality_apply]
  simp only [Opposite.op_unop]
  rfl

/-- Restrict the actual morphism to its submodule preimage. -/
def comapLift (N : P.Submodule) (f : M ⟶ P) :
    (N.comap f).toPresheafOfModules ⟶ N.toPresheafOfModules where
  app X := ModuleCat.ofHom
    ((f.app X).hom.restrict (p := (N.comap f).obj X) (q := N.obj X) (fun _ hx => hx))
  naturality g := by
    ext x
    apply Subtype.ext
    exact PresheafOfModules.naturality_apply f g x.val

/-- The restriction to the actual preimage commutes with both inclusions. -/
@[reassoc] theorem comapLift_ι (N : P.Submodule) (f : M ⟶ P) :
    N.comapLift f ≫ N.ι = (N.comap f).ι ≫ f := by
  ext X x
  rfl

end PresheafOfModules.Submodule

namespace SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {M P : SheafOfModules.{v} R}

/-- The full preimage of a sheaf submodule; sheaf locality is earned from
the same actual image section and its membership sieve. -/
def comap (N : P.Submodule) (f : M ⟶ P) : M.Submodule where
  toSubmodule := N.toSubmodule.comap f.val
  isSheaf := by
    intro X x hx
    apply N.isSheaf ((f.val.app X) x)
    rw [← PresheafOfModules.Submodule.comap_sieveOfSection N.toSubmodule f.val x]
    exact hx

/-- The sheaf preimage uses the same underlying presheaf submodule preimage. -/
theorem comap_toSubmodule (N : P.Submodule) (f : M ⟶ P) :
    (N.comap f).toSubmodule = N.toSubmodule.comap f.val := rfl

/-- The actual map from the full preimage sheaf to the original submodule. -/
def comapLift (N : P.Submodule) (f : M ⟶ P) :
    (N.comap f).toSheafOfModules ⟶ N.toSheafOfModules where
  val := N.toSubmodule.comapLift f.val

/-- Both original sheaf inclusions commute with the map from the full preimage. -/
@[reassoc] theorem comapLift_ι (N : P.Submodule) (f : M ⟶ P) :
    N.comapLift f ≫ N.ι = (N.comap f).ι ≫ f := by
  apply (SheafOfModules.forget R).map_injective
  exact PresheafOfModules.Submodule.comapLift_ι N.toSubmodule f.val

end SheafOfModules.Submodule
