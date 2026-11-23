/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedSpectralSequence

/-!
# Naturality of the degreewise forgotten coefficient bar

The canonical comparison from the underlying additive group of a
module-valued coefficient-bar coproduct to the bar of the forgotten
coefficients is natural in the coefficient system.  This file treats only
the degreewise bar objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace CategoryTheory
namespace SInverseS

variable {J A : Type u} [Category.{u} J] [CommRing A]
  {M N : J ⥤ ModuleCat.{u} A}


/-- The degreewise coefficient-bar forgetful comparison is natural in the
coefficient system. -/
theorem coefficientBarForgetObjIso_hom_naturality
    (α : M ⟶ N) (k : ℕ) :
    ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map (CategoryHomology.coefficientBarMap α k) ≫
        (coefficientBarForgetObjIso N k).hom =
      (coefficientBarForgetObjIso M k).hom ≫
        CategoryHomology.coefficientBarMap
          (Functor.whiskerRight α (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) k := by
  apply (cancel_epi (coefficientBarForgetObjIso M k).inv).1
  rw [Iso.inv_hom_id_assoc]
  apply CategoryHomology.coefficientBar_hom_ext (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))
  intro F
  rw [← Category.assoc,
    coefficientBarι_comp_coefficientBarForgetObjIso_inv]
  rw [← Category.assoc, ← ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map_comp]
  rw [CategoryHomology.coefficientBarι_map]
  rw [((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map_comp, Category.assoc,
    map_coefficientBarι_comp_coefficientBarForgetObjIso_hom]
  rw [CategoryHomology.coefficientBarι_map]
  rfl

end SInverseS
end CategoryTheory

end
