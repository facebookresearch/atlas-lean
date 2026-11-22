/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.LocalizationProductComparison
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# The actual Cartesian choice on the original model homotopy category

The proved finite products give the ordinary homotopy category its
Cartesian monoidal structure. The SAME original fibrant product is
identified with this chosen tensor by its complete projection maps.
This structure uses genuine derived products. Native localized model
pushout-product and internal-power conditions remain separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalCategory

namespace HomotopicalAlgebra
variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The proved actual original finite products supply the Cartesian choice on the SAME model homotopy category. -/
@[instance_reducible]
def homotopyCategoryCartesian (C : Type u) [Category.{v} C] [ModelCategory C] :
    CartesianMonoidalCategory (HomotopyCategory C) :=
  CartesianMonoidalCategory.ofHasFiniteProducts (C := HomotopyCategory C)

/-- The SAME original fibrant product, with its literal projected maps, is the chosen homotopy-category tensor. -/
def nativeProductTensorIso (X Y : C) [IsFibrant X] [IsFibrant Y] :
    letI : CartesianMonoidalCategory (HomotopyCategory C) := homotopyCategoryCartesian C
    (toHomotopyCategory C).obj (X ⨯ Y) ≅ (toHomotopyCategory C).obj X ⊗ (toHomotopyCategory C).obj Y := by
  letI : CartesianMonoidalCategory (HomotopyCategory C) := homotopyCategoryCartesian C
  let Q := toHomotopyCategory C
  refine
    { hom := CartesianMonoidalCategory.lift (Q.map prod.fst) (Q.map prod.snd)
      inv := ModelLocalization.productLift Q X Y
        (CartesianMonoidalCategory.fst (Q.obj X) (Q.obj Y))
        (CartesianMonoidalCategory.snd (Q.obj X) (Q.obj Y))
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply ModelLocalization.product_hom_ext Q X Y
    · rw [Category.assoc, ModelLocalization.productLift_fst, CartesianMonoidalCategory.lift_fst,
        Category.id_comp]
    · rw [Category.assoc, ModelLocalization.productLift_snd, CartesianMonoidalCategory.lift_snd,
        Category.id_comp]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, CartesianMonoidalCategory.lift_fst, ModelLocalization.productLift_fst,
        Category.id_comp]
    · rw [Category.assoc, CartesianMonoidalCategory.lift_snd, ModelLocalization.productLift_snd,
        Category.id_comp]

/-- The complete original first projection is the first leg of the SAME native tensor isomorphism. -/
@[reassoc] theorem nativeProductTensorIso_fst (X Y : C) [IsFibrant X] [IsFibrant Y] :
    letI : CartesianMonoidalCategory (HomotopyCategory C) := homotopyCategoryCartesian C
    (nativeProductTensorIso X Y).hom ≫
      CartesianMonoidalCategory.fst ((toHomotopyCategory C).obj X) ((toHomotopyCategory C).obj Y) =
        (toHomotopyCategory C).map (prod.fst : X ⨯ Y ⟶ X) := by
  let _ : CartesianMonoidalCategory (HomotopyCategory C) := homotopyCategoryCartesian C
  exact CartesianMonoidalCategory.lift_fst _ _

/-- The complete original second projection is the second leg of the SAME native tensor isomorphism. -/
@[reassoc] theorem nativeProductTensorIso_snd (X Y : C) [IsFibrant X] [IsFibrant Y] :
    letI : CartesianMonoidalCategory (HomotopyCategory C) := homotopyCategoryCartesian C
    (nativeProductTensorIso X Y).hom ≫
      CartesianMonoidalCategory.snd ((toHomotopyCategory C).obj X) ((toHomotopyCategory C).obj Y) =
        (toHomotopyCategory C).map (prod.snd : X ⨯ Y ⟶ Y) := by
  let _ : CartesianMonoidalCategory (HomotopyCategory C) := homotopyCategoryCartesian C
  exact CartesianMonoidalCategory.lift_snd _ _

/-- Both actual original arrows retain the SAME complete native tensor-isomorphism naturality square. -/
@[reassoc] theorem nativeProductTensorIso_natural {X X' Y Y' : C}
    [IsFibrant X] [IsFibrant X'] [IsFibrant Y] [IsFibrant Y'] (f : X ⟶ X') (g : Y ⟶ Y') :
    letI : CartesianMonoidalCategory (HomotopyCategory C) := homotopyCategoryCartesian C
    (toHomotopyCategory C).map (prod.map f g) ≫ (nativeProductTensorIso X' Y').hom =
      (nativeProductTensorIso X Y).hom ≫ ((toHomotopyCategory C).map f ⊗ₘ (toHomotopyCategory C).map g) := by
  let _ : CartesianMonoidalCategory (HomotopyCategory C) := homotopyCategoryCartesian C
  let Q := toHomotopyCategory C
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, nativeProductTensorIso_fst, ← Q.map_comp, prod.map_fst, Q.map_comp,
      Category.assoc, CartesianMonoidalCategory.tensorHom_fst, ← Category.assoc, nativeProductTensorIso_fst]
  · rw [Category.assoc, nativeProductTensorIso_snd, ← Q.map_comp, prod.map_snd, Q.map_comp,
      Category.assoc, CartesianMonoidalCategory.tensorHom_snd, ← Category.assoc, nativeProductTensorIso_snd]

end HomotopicalAlgebra
