/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.Mod.FreePairRelativeTensor

/-!
# Augmenting the actual tensor of two free internal modules

Two maps from free modules to the regular module give a map from their
relative tensor to that same regular module. Under the original free-pair
comparison, its complete free generator is the product of the two original
generator maps. The actual free adjunction then identifies the whole module
arrow with the free extension of that product.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped MonoidalCategory CategoryTheory.MonObj

namespace CategoryTheory.Mod.FreePairAugmentation

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (A : CommMon C) [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The original relative-tensor monoidal structure on these same internal modules. -/
local instance moduleMonoidal : MonoidalCategory (Mod C A.X) :=
  Mod.instMonoidalCategory A

/-- The complete original pair generator is multiplied through the actual
relative-tensor unit after both original free-module arrows. -/
theorem tensor_regular_generator (P Q : C)
    (f : (Mod.free A.X).obj P ⟶ Mod.regular A.X)
    (g : (Mod.free A.X).obj Q ⟶ Mod.regular A.X) :
    Mod.FreeRelativeTensor.freeUnit A (P ⊗ Q) ≫
        ((Mod.FreePairRelativeTensor.iso A P Q).inv ≫
          (f ⊗ₘ g) ≫ (λ_ (Mod.regular A.X)).hom).hom =
      ((Mod.FreeRelativeTensor.freeUnit A P ≫ f.hom) ⊗ₘ
        (Mod.FreeRelativeTensor.freeUnit A Q ≫ g.hom)) ≫
          (Mod.regular A.X).mod.smul := by
  let f₀ : ((Mod.free A.X).obj P).X ⟶ A.X := f.hom
  let g₀ : ((Mod.free A.X).obj Q).X ⟶ A.X := g.hom
  let p := Mod.relativeTensorπ A ((Mod.free A.X).obj P) ((Mod.free A.X).obj Q)
  let p' : A.X ⊗ A.X ⟶
      (((Mod.relativeTensor A).obj (Mod.regular A.X)).obj (Mod.regular A.X)).X :=
    Mod.relativeTensorπ A (Mod.regular A.X) (Mod.regular A.X)
  let t := (Mod.relativeTensorMap A f g).hom
  let l : (((Mod.relativeTensor A).obj (Mod.regular A.X)).obj (Mod.regular A.X)).X ⟶ A.X :=
    (Mod.relativeTensorLeftUnitIso A (Mod.regular A.X)).hom.hom
  let d : A.X ⊗ A.X ⟶ A.X := (Mod.regular A.X).mod.smul
  have ht : p ≫ t = (f₀ ⊗ₘ g₀) ≫ p' :=
    Mod.relativeTensorMap_π A f g
  have hl : p' ≫ l = d :=
    Mod.relativeTensorLeftUnitor_hom_π A (Mod.regular A.X)
  change Mod.FreeRelativeTensor.freeUnit A (P ⊗ Q) ≫
      ((Mod.FreePairRelativeTensor.iso A P Q).inv.hom ≫ t ≫ l) =
    ((Mod.FreeRelativeTensor.freeUnit A P ≫ f₀) ⊗ₘ
      (Mod.FreeRelativeTensor.freeUnit A Q ≫ g₀)) ≫ d
  calc
    _ = (Mod.FreeRelativeTensor.freeUnit A P ⊗ₘ Mod.FreeRelativeTensor.freeUnit A Q) ≫
        p ≫ t ≫ l := by
      rw [← Category.assoc, Mod.FreePairRelativeTensor.iso_generator, Category.assoc]
    _ = (Mod.FreeRelativeTensor.freeUnit A P ⊗ₘ Mod.FreeRelativeTensor.freeUnit A Q) ≫
        (f₀ ⊗ₘ g₀) ≫ p' ≫ l := by
      rw [← Category.assoc p t l, ht]
      simp only [Category.assoc]
    _ = ((Mod.FreeRelativeTensor.freeUnit A P ≫ f₀) ⊗ₘ
        (Mod.FreeRelativeTensor.freeUnit A Q ≫ g₀)) ≫ d := by
      rw [hl, ← Category.assoc, tensorHom_comp_tensorHom]

/-- The whole free-pair augmentation is the original free extension of the
product of its two full original generator maps. -/
theorem tensor_regular_eq_extension (P Q : C)
    (f : (Mod.free A.X).obj P ⟶ Mod.regular A.X)
    (g : (Mod.free A.X).obj Q ⟶ Mod.regular A.X) :
    (Mod.FreePairRelativeTensor.iso A P Q).inv ≫
        (f ⊗ₘ g) ≫ (λ_ (Mod.regular A.X)).hom =
      ((Mod.freeForgetAdjunction A.X).homEquiv (P ⊗ Q) (Mod.regular A.X)).symm
        (((Mod.FreeRelativeTensor.freeUnit A P ≫ f.hom) ⊗ₘ
          (Mod.FreeRelativeTensor.freeUnit A Q ≫ g.hom)) ≫
            (Mod.regular A.X).mod.smul) := by
  apply ((Mod.freeForgetAdjunction A.X).homEquiv (P ⊗ Q) (Mod.regular A.X)).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact tensor_regular_generator A P Q f g

/-- Both complete free arrows preserve the original left unit and the
actual target action, without restricting the second target to the regular module. -/
theorem tensor_left_unit_generator (P Q : C) (N : Mod C A.X)
    (f : (Mod.free A.X).obj P ⟶ Mod.regular A.X) (g : (Mod.free A.X).obj Q ⟶ N) :
    Mod.FreeRelativeTensor.freeUnit A (P ⊗ Q) ≫
        ((Mod.FreePairRelativeTensor.iso A P Q).inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom).hom =
      ((Mod.FreeRelativeTensor.freeUnit A P ≫ f.hom) ⊗ₘ
        (Mod.FreeRelativeTensor.freeUnit A Q ≫ g.hom)) ≫ N.mod.smul := by
  let f₀ : ((Mod.free A.X).obj P).X ⟶ A.X := f.hom
  let g₀ : ((Mod.free A.X).obj Q).X ⟶ N.X := g.hom
  let p := Mod.relativeTensorπ A ((Mod.free A.X).obj P) ((Mod.free A.X).obj Q)
  let p' : A.X ⊗ N.X ⟶ (((Mod.relativeTensor A).obj (Mod.regular A.X)).obj N).X :=
    Mod.relativeTensorπ A (Mod.regular A.X) N
  let t := (Mod.relativeTensorMap A f g).hom
  let l : (((Mod.relativeTensor A).obj (Mod.regular A.X)).obj N).X ⟶ N.X :=
    (Mod.relativeTensorLeftUnitIso A N).hom.hom
  let d : A.X ⊗ N.X ⟶ N.X := N.mod.smul
  have ht : p ≫ t = (f₀ ⊗ₘ g₀) ≫ p' := Mod.relativeTensorMap_π A f g
  have hl : p' ≫ l = d := Mod.relativeTensorLeftUnitor_hom_π A N
  change Mod.FreeRelativeTensor.freeUnit A (P ⊗ Q) ≫
      ((Mod.FreePairRelativeTensor.iso A P Q).inv.hom ≫ t ≫ l) =
    ((Mod.FreeRelativeTensor.freeUnit A P ≫ f₀) ⊗ₘ
      (Mod.FreeRelativeTensor.freeUnit A Q ≫ g₀)) ≫ d
  calc
    _ = (Mod.FreeRelativeTensor.freeUnit A P ⊗ₘ Mod.FreeRelativeTensor.freeUnit A Q) ≫
        p ≫ t ≫ l := by
      rw [← Category.assoc, Mod.FreePairRelativeTensor.iso_generator, Category.assoc]
    _ = (Mod.FreeRelativeTensor.freeUnit A P ⊗ₘ Mod.FreeRelativeTensor.freeUnit A Q) ≫
        (f₀ ⊗ₘ g₀) ≫ p' ≫ l := by
      rw [← Category.assoc p t l, ht]
      simp only [Category.assoc]
    _ = ((Mod.FreeRelativeTensor.freeUnit A P ≫ f₀) ⊗ₘ
        (Mod.FreeRelativeTensor.freeUnit A Q ≫ g₀)) ≫ d := by
      rw [hl, ← Category.assoc, tensorHom_comp_tensorHom]

/-- The full original left-unit pair arrow is the actual free extension
of its two original coefficient maps and the complete target module action. -/
theorem tensor_left_unit_eq_extension (P Q : C) (N : Mod C A.X)
    (f : (Mod.free A.X).obj P ⟶ Mod.regular A.X) (g : (Mod.free A.X).obj Q ⟶ N) :
    (Mod.FreePairRelativeTensor.iso A P Q).inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom =
      ((Mod.freeForgetAdjunction A.X).homEquiv (P ⊗ Q) N).symm
        (((Mod.FreeRelativeTensor.freeUnit A P ≫ f.hom) ⊗ₘ
          (Mod.FreeRelativeTensor.freeUnit A Q ≫ g.hom)) ≫ N.mod.smul) := by
  apply ((Mod.freeForgetAdjunction A.X).homEquiv (P ⊗ Q) N).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact tensor_left_unit_generator A P Q N f g

/-- The full right-unit arrow retains the original coefficient/right-scalar
braid and unchanged target action after both original free generators. -/
theorem tensor_right_unit_generator (P Q : C) (N : Mod C A.X)
    (f : (Mod.free A.X).obj P ⟶ N) (g : (Mod.free A.X).obj Q ⟶ Mod.regular A.X) :
    Mod.FreeRelativeTensor.freeUnit A (P ⊗ Q) ≫
        ((Mod.FreePairRelativeTensor.iso A P Q).inv ≫ (f ⊗ₘ g) ≫ (ρ_ N).hom).hom =
      ((Mod.FreeRelativeTensor.freeUnit A P ≫ f.hom) ⊗ₘ
        (Mod.FreeRelativeTensor.freeUnit A Q ≫ g.hom)) ≫ (β_ N.X A.X).hom ≫ N.mod.smul := by
  let f₀ : ((Mod.free A.X).obj P).X ⟶ N.X := f.hom
  let g₀ : ((Mod.free A.X).obj Q).X ⟶ A.X := g.hom
  let p := Mod.relativeTensorπ A ((Mod.free A.X).obj P) ((Mod.free A.X).obj Q)
  let p' : N.X ⊗ A.X ⟶ (((Mod.relativeTensor A).obj N).obj (Mod.regular A.X)).X :=
    Mod.relativeTensorπ A N (Mod.regular A.X)
  let t := (Mod.relativeTensorMap A f g).hom
  let r : (((Mod.relativeTensor A).obj N).obj (Mod.regular A.X)).X ⟶ N.X :=
    (Mod.relativeTensorRightUnitIso A N).hom.hom
  let d : N.X ⊗ A.X ⟶ N.X := (β_ N.X A.X).hom ≫ N.mod.smul
  have ht : p ≫ t = (f₀ ⊗ₘ g₀) ≫ p' := Mod.relativeTensorMap_π A f g
  have hr : p' ≫ r = d := Mod.relativeTensorRightUnitor_hom_π A N
  change Mod.FreeRelativeTensor.freeUnit A (P ⊗ Q) ≫
      ((Mod.FreePairRelativeTensor.iso A P Q).inv.hom ≫ t ≫ r) =
    ((Mod.FreeRelativeTensor.freeUnit A P ≫ f₀) ⊗ₘ
      (Mod.FreeRelativeTensor.freeUnit A Q ≫ g₀)) ≫ d
  calc
    _ = (Mod.FreeRelativeTensor.freeUnit A P ⊗ₘ Mod.FreeRelativeTensor.freeUnit A Q) ≫
        p ≫ t ≫ r := by
      rw [← Category.assoc, Mod.FreePairRelativeTensor.iso_generator, Category.assoc]
    _ = (Mod.FreeRelativeTensor.freeUnit A P ⊗ₘ Mod.FreeRelativeTensor.freeUnit A Q) ≫
        (f₀ ⊗ₘ g₀) ≫ p' ≫ r := by
      rw [← Category.assoc p t r, ht]
      simp only [Category.assoc]
    _ = ((Mod.FreeRelativeTensor.freeUnit A P ≫ f₀) ⊗ₘ
        (Mod.FreeRelativeTensor.freeUnit A Q ≫ g₀)) ≫ d := by
      rw [hr, ← Category.assoc, tensorHom_comp_tensorHom]

/-- The complete original right-unit pair arrow is the actual free extension
with its original coefficient/scalar braid and full target action. -/
theorem tensor_right_unit_eq_extension (P Q : C) (N : Mod C A.X)
    (f : (Mod.free A.X).obj P ⟶ N) (g : (Mod.free A.X).obj Q ⟶ Mod.regular A.X) :
    (Mod.FreePairRelativeTensor.iso A P Q).inv ≫ (f ⊗ₘ g) ≫ (ρ_ N).hom =
      ((Mod.freeForgetAdjunction A.X).homEquiv (P ⊗ Q) N).symm
        (((Mod.FreeRelativeTensor.freeUnit A P ≫ f.hom) ⊗ₘ
          (Mod.FreeRelativeTensor.freeUnit A Q ≫ g.hom)) ≫
            (β_ N.X A.X).hom ≫ N.mod.smul) := by
  apply ((Mod.freeForgetAdjunction A.X).homEquiv (P ⊗ Q) N).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact tensor_right_unit_generator A P Q N f g

end CategoryTheory.Mod.FreePairAugmentation
