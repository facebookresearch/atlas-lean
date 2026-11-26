/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Monoidal.ComonObjIso

/-!
# The comonoid morphism of an isomorphism transport

Let `e : M ≅ X` be an isomorphism in a monoidal category and let `M` have a comonoid
structure. Equip `X` with the transported counit and comultiplication.

The map `e.hom` then preserves the counit and comultiplication, so it is a comonoid morphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.ComonObj

variable {C : Type*} [Category* C] [MonoidalCategory C]

/-- The forward comonoid map of an isomorphism transport.

With `X` equipped by `ComonObj.ofIso e`, the forward isomorphism map `e.hom` is a comonoid
homomorphism. -/
theorem isComonHom_ofIso {M X : C} [ComonObj M] (e : M ≅ X) :
    letI : ComonObj X := ComonObj.ofIso e
    IsComonHom e.hom := by
  letI : ComonObj X := ComonObj.ofIso e
  constructor
  · change e.hom ≫ (e.inv ≫ ComonObj.counit (X := M)) = ComonObj.counit (X := M)
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · change e.hom ≫ (e.inv ≫ ComonObj.comul (X := M) ≫ (e.hom ⊗ₘ e.hom)) =
      ComonObj.comul (X := M) ≫ (e.hom ⊗ₘ e.hom)
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end CategoryTheory.ComonObj
