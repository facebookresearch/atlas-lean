/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Monoidal.PushoutProduct
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Initial maps and the pushout-product

An initial map has a fixed-left tensor map as its pushout-product when
the two tensor objects from its initial source are initial. The comparison
uses the selected pushout and is the identity on the target.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory

namespace CategoryTheory.MonoidalCategory.Arrow.PushoutProduct

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasPushouts C]

/-- Compare the pushout-product against an initial map with fixed-left tensor,
using the two actual initial tensor objects. -/
noncomputable def isInitialIsoOfTensor
    (X : CategoryTheory.Arrow C) {I : C} (hI : IsInitial I) {K : C}
    (hA : IsInitial (I ⊗ X.left)) (hB : IsInitial (I ⊗ X.right)) :
    (CategoryTheory.Arrow.mk (hI.to K) □ X) ≅
      CategoryTheory.Arrow.mk (K ◁ X.hom) := by
  let F := curriedTensor C
  let hA' : IsInitial ((F.obj I).obj X.left) := hA
  let hB' : IsInitial ((F.obj I).obj X.right) := hB
  let _ : IsIso ((F.obj I).map X.hom) := isIso_of_isInitial hA' hB' _
  have hp : IsPushout ((F.map (hI.to K)).app X.left) ((F.obj I).map X.hom)
      (𝟙 ((F.obj K).obj X.left)) (hB'.to ((F.obj K).obj X.left)) :=
    .of_vert_isIso (sq := ⟨hA'.hom_ext _ _⟩)
  let d : pushout ((F.map (hI.to K)).app X.left) ((F.obj I).map X.hom) ⟶
      (F.obj K).obj X.right :=
    pushout.desc ((F.obj K).map X.hom) ((F.map (hI.to K)).app X.right)
      ((F.map (hI.to K)).naturality X.hom).symm
  have hcomm : hp.isoPushout.inv ≫ (F.obj K).map X.hom = d := by
    apply pushout.hom_ext
    · rw [hp.inl_isoPushout_inv_assoc, Category.id_comp]
      dsimp only [d]
      rw [pushout.inl_desc]
    · exact hB'.hom_ext _ _
  exact CategoryTheory.Arrow.isoMk' d ((F.obj K).map X.hom)
    hp.isoPushout.symm (Iso.refl _)
      (by simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id] using hcomm)

/-- The comparison preserves the target literally. -/
@[simp]
theorem isInitialIsoOfTensor_hom_right
    (X : CategoryTheory.Arrow C) {I : C} (hI : IsInitial I) {K : C}
    (hA : IsInitial (I ⊗ X.left)) (hB : IsInitial (I ⊗ X.right)) :
    (isInitialIsoOfTensor X hI (K := K) hA hB).hom.right =
      𝟙 (K ⊗ X.right) :=
  rfl

/-- Empty-diagram preservation supplies the two initial tensor objects. -/
noncomputable def isInitialIsoOfPreservesInitial
    (X : CategoryTheory.Arrow C) {I : C} (hI : IsInitial I) {K : C}
    [PreservesColimit (Functor.empty.{0} C) (tensorRight X.left)]
    [PreservesColimit (Functor.empty.{0} C) (tensorRight X.right)] :
    (CategoryTheory.Arrow.mk (hI.to K) □ X) ≅
      CategoryTheory.Arrow.mk (K ◁ X.hom) :=
  isInitialIsoOfTensor X hI
    (IsInitial.isInitialObj (tensorRight X.left) I hI)
    (IsInitial.isInitialObj (tensorRight X.right) I hI)

end CategoryTheory.MonoidalCategory.Arrow.PushoutProduct

namespace CategoryTheory.MonoidalCategory.Arrow.PushoutProduct

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasPushouts C]

/-- The right initial-map comparison uses the literal horizontal pushout.
Its target is the original right tensor object, with identity comparison. -/
noncomputable def isInitialRightIsoOfTensor
    (X : CategoryTheory.Arrow C) {I : C} (hI : IsInitial I) {K : C}
    (hA : IsInitial (X.left ⊗ I)) (hB : IsInitial (X.right ⊗ I)) :
    (X □ CategoryTheory.Arrow.mk (hI.to K)) ≅
      CategoryTheory.Arrow.mk (X.hom ▷ K) := by
  let F := curriedTensor C
  let hA' : IsInitial ((F.obj X.left).obj I) := hA
  let hB' : IsInitial ((F.obj X.right).obj I) := hB
  let _ : IsIso ((F.map X.hom).app I) := isIso_of_isInitial hA' hB' _
  have hp : IsPushout ((F.map X.hom).app I) ((F.obj X.left).map (hI.to K))
      (hB'.to ((F.obj X.left).obj K)) (𝟙 ((F.obj X.left).obj K)) :=
    .of_horiz_isIso (sq := ⟨hA'.hom_ext _ _⟩)
  let d : pushout ((F.map X.hom).app I) ((F.obj X.left).map (hI.to K)) ⟶
      (F.obj X.right).obj K :=
    pushout.desc ((F.obj X.right).map (hI.to K)) ((F.map X.hom).app K)
      ((F.map X.hom).naturality (hI.to K)).symm
  have hcomm : hp.isoPushout.inv ≫ (F.map X.hom).app K = d := by
    apply pushout.hom_ext
    · exact hB'.hom_ext _ _
    · rw [hp.inr_isoPushout_inv_assoc, Category.id_comp]
      dsimp only [d]
      rw [pushout.inr_desc]
  exact CategoryTheory.Arrow.isoMk' d ((F.map X.hom).app K)
    hp.isoPushout.symm (Iso.refl _)
      (by simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id] using hcomm)

/-- The right initial-map comparison leaves the target unchanged. -/
@[simp]
theorem isInitialRightIsoOfTensor_hom_right
    (X : CategoryTheory.Arrow C) {I : C} (hI : IsInitial I) {K : C}
    (hA : IsInitial (X.left ⊗ I)) (hB : IsInitial (X.right ⊗ I)) :
    (isInitialRightIsoOfTensor X hI (K := K) hA hB).hom.right =
      𝟙 (X.right ⊗ K) :=
  rfl

/-- The inverse right comparison also has the original target map. -/
@[simp]
theorem isInitialRightIsoOfTensor_inv_right
    (X : CategoryTheory.Arrow C) {I : C} (hI : IsInitial I) {K : C}
    (hA : IsInitial (X.left ⊗ I)) (hB : IsInitial (X.right ⊗ I)) :
    (isInitialRightIsoOfTensor X hI (K := K) hA hB).inv.right =
      𝟙 (X.right ⊗ K) :=
  rfl

/-- Empty-diagram preservation supplies the literal initial tensor objects
for the right initial-map comparison. -/
noncomputable def isInitialRightIsoOfPreservesInitial
    (X : CategoryTheory.Arrow C) {I : C} (hI : IsInitial I) {K : C}
    [PreservesColimit (Functor.empty.{0} C) (tensorLeft X.left)]
    [PreservesColimit (Functor.empty.{0} C) (tensorLeft X.right)] :
    (X □ CategoryTheory.Arrow.mk (hI.to K)) ≅
      CategoryTheory.Arrow.mk (X.hom ▷ K) :=
  isInitialRightIsoOfTensor X hI
    (IsInitial.isInitialObj (tensorLeft X.left) I hI)
    (IsInitial.isInitialObj (tensorLeft X.right) I hI)

end CategoryTheory.MonoidalCategory.Arrow.PushoutProduct
