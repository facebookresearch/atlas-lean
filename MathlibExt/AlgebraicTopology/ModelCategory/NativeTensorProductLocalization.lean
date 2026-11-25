/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategoryCartesian

/-!
# Literal original tensor comparisons at native fibrant pairs

The original Cartesian category identifies its tensor with its product.
The actual model-localized fibrant product gives the chosen homotopy
tensor. Both full original projection legs identify the resulting map
with the literal Cartesian product comparison. Only the two native
objects are fibrant; no Cartesian model axiom is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalCategory

namespace HomotopicalAlgebra.NativeTensorProductLocalization
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- The complete first original projection of the actual tensor-to-product isomorphism. -/
theorem tensorProductIso_fst (X Y : C) :
    ((CartesianMonoidalCategory.tensorLeftIsoProd X).app Y).hom ≫ prod.fst =
      CartesianMonoidalCategory.fst X Y :=
  IsLimit.conePointUniqueUpToIso_hom_comp (CartesianMonoidalCategory.tensorProductIsBinaryProduct
    X Y)
    (limit.isLimit (pair X Y)) ⟨WalkingPair.left⟩

/-- The complete second original projection of the actual tensor-to-product isomorphism. -/
theorem tensorProductIso_snd (X Y : C) :
    ((CartesianMonoidalCategory.tensorLeftIsoProd X).app Y).hom ≫ prod.snd =
      CartesianMonoidalCategory.snd X Y :=
  IsLimit.conePointUniqueUpToIso_hom_comp (CartesianMonoidalCategory.tensorProductIsBinaryProduct
    X Y)
    (limit.isLimit (pair X Y)) ⟨WalkingPair.right⟩

variable [ModelCategory C]

/-- The SAME original fibrant tensor is the chosen homotopy-category tensor through both actual
product isomorphisms. -/
def nativeTensorIso (X Y : C) [IsFibrant X] [IsFibrant Y] :
    letI : CartesianMonoidalCategory ((weakEquivalences C).Localization) :=
      homotopyCategoryCartesian C
    ((weakEquivalences C).Q).obj (X ⊗ Y) ≅
      ((weakEquivalences C).Q).obj X ⊗ ((weakEquivalences C).Q).obj Y := by
  letI : CartesianMonoidalCategory ((weakEquivalences C).Localization) :=
      homotopyCategoryCartesian C
  exact ((weakEquivalences C).Q).mapIso ((CartesianMonoidalCategory.tensorLeftIsoProd X).app Y) ≪≫
    nativeProductTensorIso X Y

/-- The SAME complete first original tensor projection survives both actual localization
isomorphisms. -/
@[reassoc] theorem nativeTensorIso_fst (X Y : C) [IsFibrant X] [IsFibrant Y] :
    letI : CartesianMonoidalCategory ((weakEquivalences C).Localization) :=
      homotopyCategoryCartesian C
    (nativeTensorIso X Y).hom ≫
      CartesianMonoidalCategory.fst (((weakEquivalences C).Q).obj X)
        (((weakEquivalences C).Q).obj Y) =
    ((weakEquivalences C).Q).map (CartesianMonoidalCategory.fst X Y) := by
  let _ : CartesianMonoidalCategory ((weakEquivalences C).Localization) :=
      homotopyCategoryCartesian C
  change (((weakEquivalences C).Q).map ((CartesianMonoidalCategory.tensorLeftIsoProd X).app Y).hom ≫
    (nativeProductTensorIso X Y).hom) ≫ _ = _
  rw [Category.assoc, nativeProductTensorIso_fst, ← Functor.map_comp, tensorProductIso_fst]

/-- The SAME complete second original tensor projection survives both actual localization
isomorphisms. -/
@[reassoc] theorem nativeTensorIso_snd (X Y : C) [IsFibrant X] [IsFibrant Y] :
    letI : CartesianMonoidalCategory ((weakEquivalences C).Localization) :=
      homotopyCategoryCartesian C
    (nativeTensorIso X Y).hom ≫
      CartesianMonoidalCategory.snd (((weakEquivalences C).Q).obj X)
        (((weakEquivalences C).Q).obj Y) =
    ((weakEquivalences C).Q).map (CartesianMonoidalCategory.snd X Y) := by
  let _ : CartesianMonoidalCategory ((weakEquivalences C).Localization) :=
      homotopyCategoryCartesian C
  change (((weakEquivalences C).Q).map ((CartesianMonoidalCategory.tensorLeftIsoProd X).app Y).hom ≫
    (nativeProductTensorIso X Y).hom) ≫ _ = _
  rw [Category.assoc, nativeProductTensorIso_snd, ← Functor.map_comp, tensorProductIso_snd]

/-- Both full original projections identify the SAME native isomorphism map with the literal
Cartesian comparison. -/
theorem nativeTensorIso_hom (X Y : C) [IsFibrant X] [IsFibrant Y] :
    letI : CartesianMonoidalCategory ((weakEquivalences C).Localization) :=
      homotopyCategoryCartesian C
    (nativeTensorIso X Y).hom = CartesianMonoidalCategory.prodComparison ((weakEquivalences C).Q) X
      Y := by
  let _ : CartesianMonoidalCategory ((weakEquivalences C).Localization) :=
      homotopyCategoryCartesian C
  apply CartesianMonoidalCategory.hom_ext
  · rw [nativeTensorIso_fst, CartesianMonoidalCategory.prodComparison_fst]
  · rw [nativeTensorIso_snd, CartesianMonoidalCategory.prodComparison_snd]

/-- The literal original Cartesian localization comparison is invertible at every genuine native
fibrant pair. -/
theorem comparison_isIso_of_fibrant (X Y : C) [IsFibrant X] [IsFibrant Y] :
    letI : CartesianMonoidalCategory ((weakEquivalences C).Localization) :=
      homotopyCategoryCartesian C
    IsIso (CartesianMonoidalCategory.prodComparison ((weakEquivalences C).Q) X Y) := by
  let _ : CartesianMonoidalCategory ((weakEquivalences C).Localization) :=
      homotopyCategoryCartesian C
  rw [← nativeTensorIso_hom X Y]
  infer_instance

end HomotopicalAlgebra.NativeTensorProductLocalization
