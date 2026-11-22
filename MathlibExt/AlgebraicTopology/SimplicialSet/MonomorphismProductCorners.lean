/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct
public import Mathlib.CategoryTheory.Adhesive.PushoutProduct

/-!
# Product corners and their image unions

The actual pushout-product of two monomorphisms is identified, over its
unchanged product target, with the union of their image subcomplexes.
Native range factorizations and native pushout transport supply the
comparison; native adhesive monicity supplies its monomorphism assertion.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace SSet

variable {A B K L : SSet.{u}} (i : A ⟶ B) (j : K ⟶ L) [Mono i] [Mono j]

/-- The actual product corner is the union of the two image subcomplexes. -/
def pushoutProductUnionIso :
    (Arrow.mk i □ Arrow.mk j) ≅
      Arrow.mk ((Subcomplex.range i).unionProd (Subcomplex.range j)).ι := by
  let eᵢ : Arrow.mk i ≅ Arrow.mk (Subcomplex.range i).ι :=
    Arrow.isoMk' i (Subcomplex.range i).ι
      (asIso (Subcomplex.toRange i)) (Iso.refl B) (by simp)
  let eⱼ : Arrow.mk j ≅ Arrow.mk (Subcomplex.range j).ι :=
    Arrow.isoMk' j (Subcomplex.range j).ι
      (asIso (Subcomplex.toRange j)) (Iso.refl L) (by simp)
  let sq₀ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i j
  let sq₁ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
    (Subcomplex.range i).ι j
  let E₀ := Functor.PushoutObjObj.ι_iso_of_iso_left
    (F := curriedTensor SSet.{u}) (f₁ := Arrow.mk i)
    (f₁' := Arrow.mk (Subcomplex.range i).ι) (f₂ := Arrow.mk j) sq₀ sq₁ eᵢ
  let E₁ := Functor.PushoutObjObj.ι_iso_of_iso_right
    (F := curriedTensor SSet.{u}) (f₁ := Arrow.mk (Subcomplex.range i).ι)
    (f₂ := Arrow.mk j) (f₂' := Arrow.mk (Subcomplex.range j).ι) sq₁
    (Subcomplex.unionProd.pushoutObjObj (Subcomplex.range i) (Subcomplex.range j)) eⱼ
  exact E₀ ≪≫ E₁

/-- The union comparison leaves the actual product target fixed. -/
@[simp]
lemma pushoutProductUnionIso_hom_right :
    (pushoutProductUnionIso i j).hom.right = 𝟙 (B ⊗ L) := by
  simp [pushoutProductUnionIso]

/-- The source comparison commutes strictly with the union inclusion. -/
@[reassoc (attr := simp)]
lemma pushoutProductUnionIso_hom_left_comp_ι :
    (pushoutProductUnionIso i j).hom.left ≫
        ((Subcomplex.range i).unionProd (Subcomplex.range j)).ι =
      (Arrow.mk i □ Arrow.mk j).hom := by
  simp

/-- Product corners are monic and their specified pushout domains are the image unions. -/
lemma monomorphism_product_corner :
    Mono (Arrow.mk i □ Arrow.mk j).hom ∧
      ∃ e : (Arrow.mk i □ Arrow.mk j).left ≅
          ((Subcomplex.range i).unionProd (Subcomplex.range j) : SSet.{u}),
        e.hom ≫ ((Subcomplex.range i).unionProd (Subcomplex.range j)).ι =
          (Arrow.mk i □ Arrow.mk j).hom := by
  refine ⟨?_, Arrow.leftFunc.mapIso (pushoutProductUnionIso i j),
    pushoutProductUnionIso_hom_left_comp_ι i j⟩
  have : Mono (Arrow.mk i).hom := by simpa only [Arrow.mk_hom] using (inferInstance : Mono i)
  have : Mono (Arrow.mk j).hom := by simpa only [Arrow.mk_hom] using (inferInstance : Mono j)
  exact MonoidalCategory.Arrow.PushoutProduct.instMonoHomObjArrowFunctorPushoutProduct
    (C := SSet.{u}) (X := Arrow.mk i) (Y := Arrow.mk j)

end SSet
