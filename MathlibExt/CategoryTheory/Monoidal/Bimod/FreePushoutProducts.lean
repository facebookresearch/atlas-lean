/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.FreeTensor
public import Mathlib.CategoryTheory.Monoidal.PushoutProduct

/-!
# Original free bimodule pushout-products

The complete free-pair tensor isomorphism identifies the original
bimodule Leibniz arrow with the free outer image of the base pushout
product against the middle scalar coefficient. Both actual pushout
cofans, the original attaching map and all four source comparisons remain.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped MonoidalCategory

namespace Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasColimitsOfSize.{0, 0} C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (A B D : Mon C)

local instance targetColimits : HasColimitsOfSize.{0, 0} (Bimod A D) := Bimod.hasColimits A D

/-- The actual original free-pair Leibniz arrow is the free outer image of the coefficient pushout-product. -/
def freePushoutProductIso {U V X Y : C} (i : U ⟶ V) (j : X ⟶ Y) :
    Arrow.mk ((free A D).map (Arrow.mk i □ Arrow.mk (B.X ◁ j)).hom) ≅
      ((tensorCurried A B D).leibnizPushout.obj (Arrow.mk ((free A B).map i))).obj
        (Arrow.mk ((free B D).map j)) := by
  let F := free A D
  let e (P Q : C) := (freePairTensorIso A B D P Q).symm
  have hleft {P P' Q : C} (f : P ⟶ P') :
      F.map (f ▷ (B.X ⊗ Q)) ≫ (e P' Q).hom =
        (e P Q).hom ≫ whiskerRight ((free A B).map f) (freeObject B D Q) := by
    have h := freePairTensorIso_naturality A B D f (𝟙 Q)
    simp only [CategoryTheory.Functor.map_id, tensorMap, whiskerLeft_id_bimod, Category.comp_id,
      whiskerLeft_id, tensorHom_id] at h
    dsimp only [free] at h
    apply (cancel_mono (freePairTensorIso A B D P' Q).hom).mp
    dsimp only [e, F, free]
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    erw [h]
    simp only [Iso.inv_hom_id_assoc]
  have hright {P Q Q' : C} (g : Q ⟶ Q') :
      F.map (P ◁ (B.X ◁ g)) ≫ (e P Q').hom =
        (e P Q).hom ≫ whiskerLeft (freeObject A B P) ((free B D).map g) := by
    have h := freePairTensorIso_naturality A B D (𝟙 P) g
    simp only [CategoryTheory.Functor.map_id, tensorMap, id_whiskerRight_bimod, Category.id_comp,
      id_tensorHom] at h
    dsimp only [free] at h
    apply (cancel_mono (freePairTensorIso A B D P Q').hom).mp
    dsimp only [e, F, free]
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    erw [h]
    simp only [Iso.inv_hom_id_assoc]
  let S := Functor.PushoutObjObj.ofHasPushout (curriedTensor C) i (B.X ◁ j)
  let R := Functor.PushoutObjObj.ofHasPushout (tensorCurried A B D)
    ((free A B).map i) ((free B D).map j)
  let mapped := F.map_isPushout S.isPushout
  have raw : IsPushout (F.map (i ▷ (B.X ⊗ X))) (F.map (U ◁ (B.X ◁ j)))
      ((e V X).hom ≫ R.inl) ((e U Y).hom ≫ R.inr) :=
    R.isPushout.of_iso' (e U X) (e V X) (e U Y) (Iso.refl R.pt)
      (hleft i).symm (hright j).symm
      (by simp only [Iso.refl_hom, Category.comp_id])
      (by simp only [Iso.refl_hom, Category.comp_id])
  let eDom := mapped.isoIsPushout _ _ raw
  have h₁ : F.map S.inl ≫ eDom.hom = (e V X).hom ≫ R.inl :=
    mapped.inl_isoIsPushout_hom _ _ raw
  have h₂ : F.map S.inr ≫ eDom.hom = (e U Y).hom ≫ R.inr :=
    mapped.inr_isoIsPushout_hom _ _ raw
  have hCorner : eDom.hom ≫ R.ι = F.map S.ι ≫ (e V Y).hom := by
    apply mapped.hom_ext
    · rw [← Category.assoc, h₁, Category.assoc, R.inl_ι]
      rw [← Category.assoc, ← F.map_comp, S.inl_ι]
      exact (hright j).symm
    · rw [← Category.assoc, h₂, Category.assoc, R.inr_ι]
      rw [← Category.assoc, ← F.map_comp, S.inr_ι]
      exact (hleft i).symm
  exact Arrow.isoMk eDom (e V Y) hCorner

end Bimod
