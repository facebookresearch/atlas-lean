/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Elements

/-!
# Elements under a natural isomorphism

A natural isomorphism between Type-valued functors induces an equivalence of
their total element types, preserving the original indexing object.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w

open CategoryTheory

namespace CategoryTheory.Functor.Elements

variable {C : Type u} [Category.{v} C] {F G : C ⥤ Type w}

/-- The equivalence of total element types induced by a natural isomorphism. -/
def equivOfIso (i : F ≅ G) : F.Elements ≃ G.Elements where
  toFun z := i.hom.mapElements.obj z
  invFun z := i.inv.mapElements.obj z
  left_inv z := by
    cases z with
    | mk val =>
      change (⟨i.inv.app _ (i.hom.app _ val)⟩ : F.Elements) = ⟨val⟩
      refine Functor.Elements.ext (F := F) _ _ rfl ?_
      simp only [eqToHom_refl]
      simp
  right_inv z := by
    cases z with
    | mk val =>
      change (⟨i.hom.app _ (i.inv.app _ val)⟩ : G.Elements) = ⟨val⟩
      refine Functor.Elements.ext (F := G) _ _ rfl ?_
      simp only [eqToHom_refl]
      simp

@[simp]
theorem equivOfIso_apply_obj (i : F ≅ G) (z : F.Elements) :
    (equivOfIso i z).obj = z.obj :=
  rfl

@[simp]
theorem equivOfIso_symm_apply_obj (i : F ≅ G) (z : G.Elements) :
    ((equivOfIso i).symm z).obj = z.obj :=
  rfl

end CategoryTheory.Functor.Elements
