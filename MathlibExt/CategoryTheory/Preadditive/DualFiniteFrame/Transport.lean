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
/-!
# Isomorphic points of finite biproduct frames

In a preadditive category, a bicone of finitely many copies of U can be
transported from its point A to an isomorphic object M.
For e:A ≅ M, its inclusions become e∘ι_i and its projections become
π_i∘e⁻¹. If the original bicone is a biproduct bilimit, the transported
bicone is a bilimit as well.
-/

@[expose] public section
noncomputable section
open CategoryTheory Limits
namespace CategoryTheory.DualFiniteFrame
section

variable {C : Type*} [Category C] [Preadditive C]
  {I : Type*} [Fintype I] {U : C} {M : C}

/-- In a preadditive category C, for finite I, an object U, a bicone b of
I copies of U and an isomorphism e:b.pt ≅ M, the transported bicone
has point M, inclusions e∘ι_i and projections π_i∘e⁻¹. -/
def transportUnitBicone (b : Bicone (fun _ : I => U)) (e : b.pt ≅ M) :
    Bicone (fun _ : I => U) where
  pt := M
  ι i := b.ι i ≫ e.hom
  π i := e.inv ≫ b.π i
  ι_π i j := by
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact b.ι_π i j

/-- In a preadditive category C, if a finite bicone b of copies of U is a
bilimit and e:b.pt ≅ M, then the transported bicone on M with
inclusions e∘ι_i and projections π_i∘e⁻¹ is also a bilimit. -/
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
