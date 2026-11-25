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
public import Mathlib.CategoryTheory.Preadditive.Biproducts
@[expose] public section
noncomputable section
open CategoryTheory Limits
namespace CategoryTheory.DualFiniteFrame
section

variable {C : Type*} [Category C] [Preadditive C]
  {I : Type*} [Fintype I] {U : C} {M : C}

/-- Transport an actual finite unit bicone along an original object isomorphism. -/
def transportUnitBicone (b : Bicone (fun _ : I => U)) (e : b.pt ≅ M) :
    Bicone (fun _ : I => U) where
  pt := M
  ι i := b.ι i ≫ e.hom
  π i := e.inv ≫ b.π i
  ι_π i j := by
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact b.ι_π i j

/-- The transported bicone is the same genuine finite biproduct. -/
def transportUnitBiconeIsBilimit (b : Bicone (fun _ : I => U))
    (hb : b.IsBilimit) (e : b.pt ≅ M) : (transportUnitBicone b e).IsBilimit := by
  apply isBilimitOfTotal
  change (∑ i, (e.inv ≫ b.π i) ≫ (b.ι i ≫ e.hom)) = 𝟙 M
  calc
    _ = e.inv ≫ (∑ i, b.π i ≫ b.ι i) ≫ e.hom := by
      simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
    _ = e.inv ≫ 𝟙 b.pt ≫ e.hom := by rw [IsBilimit.total hb]
    _ = 𝟙 M := by rw [Category.id_comp, Iso.inv_hom_id]

end

end CategoryTheory.DualFiniteFrame
