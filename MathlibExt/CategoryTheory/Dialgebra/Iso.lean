/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Dialgebra.Basic
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Isomorphisms of dialgebras

An invertible underlying morphism has a compatible inverse. Consequently
the forgetful functor reflects isomorphisms.
-/

@[expose] public section

namespace CategoryTheory.Dialgebra

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D] {F G : C ⥤ D}
variable {X Y : Dialgebra F G}

/-- The inverse underlying morphism is compatible with the structure maps. -/
theorem inverse_compatible (f : X ⟶ Y) [IsIso f.f] :
    F.map (inv f.f) ≫ X.a = Y.a ≫ G.map (inv f.f) := by
  apply (cancel_epi (F.map f.f)).1
  simp only [← Category.assoc, Functor.map_inv, IsIso.hom_inv_id, Category.id_comp]
  rw [f.h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- Lift an underlying isomorphism compatible with the structure maps. -/
@[simps]
def isoMk (e : X.A ≅ Y.A) (h : F.map e.hom ≫ Y.a = X.a ≫ G.map e.hom) :
    X ≅ Y where
  hom := ⟨e.hom, h⟩
  inv := ⟨e.inv, by
    simpa using inverse_compatible (⟨e.hom, h⟩ : X ⟶ Y)⟩
  hom_inv_id := by
    apply Hom.ext
    exact e.hom_inv_id
  inv_hom_id := by
    apply Hom.ext
    exact e.inv_hom_id

/-- Invertibility of the underlying map implies invertibility of the dialgebra map. -/
theorem isIso_of_isIso_f (f : X ⟶ Y) [IsIso f.f] : IsIso f := by
  let e : X ≅ Y := isoMk (asIso f.f) f.h
  have he : e.hom = f := Hom.ext rfl
  rw [← he]
  infer_instance

instance : (forget F G).ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    have : IsIso f.f := hf
    exact isIso_of_isIso_f f

end CategoryTheory.Dialgebra
