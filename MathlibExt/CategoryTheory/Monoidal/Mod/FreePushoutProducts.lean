/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.Mod.FreePairRelativeTensor
import MathlibExt.CategoryTheory.MorphismProperty.PushoutProduct

/-!
# Original free module pushout-products

The actual free-pair relative tensor comparison identifies the free image
of the supplied base pushout-product with the pushout-product of the two
original free-module maps. Both original pushout legs and all coefficient
maps are retained.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory

namespace CategoryTheory.Mod.FreePushoutProducts

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasPushouts C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (A : CommMon C) [HasPushouts (Mod C A.X)]

/-- The actual balanced tensor monoidal structure used by the free-module comparison. -/
local instance moduleMonoidal : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
local instance freeLeftAdjoint : (Mod.free A.X).IsLeftAdjoint :=
  (Mod.freeForgetAdjunction A.X).isLeftAdjoint

/-- The actual free functor preserves the original entire pushout-product arrow. -/
def iso {U V X Y : C} (i : U ⟶ V) (j : X ⟶ Y) :
    Arrow.mk ((Mod.free A.X).map (Arrow.mk i □ Arrow.mk j).hom) ≅
      (Arrow.mk ((Mod.free A.X).map i) □ Arrow.mk ((Mod.free A.X).map j)) := by
  let F := Mod.free A.X
  let N := (Mod.FreePairRelativeTensor.bifunctorIso A).symm
  have hleft {P P' Q : C} (f : P ⟶ P') :
      F.map (f ▷ Q) ≫ (N.app (P', Q)).hom =
        (N.app (P, Q)).hom ≫ F.map f ▷ F.obj Q := by
    have h := N.hom.naturality ((f, 𝟙 Q) : (P, Q) ⟶ (P', Q))
    change F.map (f ⊗ₘ 𝟙 Q) ≫ (N.app (P', Q)).hom =
      (N.app (P, Q)).hom ≫ (F.map f ⊗ₘ F.map (𝟙 Q)) at h
    rw [F.map_id Q] at h
    rw [tensorHom_id (F.map f) (F.obj Q)] at h
    simpa only [tensorHom_id f Q] using h
  have hright {P Q Q' : C} (g : Q ⟶ Q') :
      F.map (P ◁ g) ≫ (N.app (P, Q')).hom =
        (N.app (P, Q)).hom ≫ F.obj P ◁ F.map g := by
    have h := N.hom.naturality ((𝟙 P, g) : (P, Q) ⟶ (P, Q'))
    change F.map (𝟙 P ⊗ₘ g) ≫ (N.app (P, Q')).hom =
      (N.app (P, Q)).hom ≫ (F.map (𝟙 P) ⊗ₘ F.map g) at h
    rw [F.map_id P] at h
    rw [id_tensorHom (F.obj P) (F.map g)] at h
    simpa only [id_tensorHom P g] using h
  let s := F.map_isPushout (IsPushout.of_hasPushout (i ▷ X) (U ◁ j))
  let e := spanExt (N.app (U, X)) (N.app (V, X)) (N.app (U, Y))
    (hleft i).symm (hright j).symm
  have hcolLeft : pushout.inl (F.map (i ▷ X)) (F.map (U ◁ j)) ≫
      (HasColimit.isoOfNatIso e).hom = (N.app (V, X)).hom ≫
        pushout.inl (F.map i ▷ F.obj X) (F.obj U ◁ F.map j) := by
    exact HasColimit.ι_isoOfNatIso_hom e WalkingSpan.left
  have hcolRight : pushout.inr (F.map (i ▷ X)) (F.map (U ◁ j)) ≫
      (HasColimit.isoOfNatIso e).hom = (N.app (U, Y)).hom ≫
        pushout.inr (F.map i ▷ F.obj X) (F.obj U ◁ F.map j) := by
    exact HasColimit.ι_isoOfNatIso_hom e WalkingSpan.right
  refine Arrow.isoMk (s.isoPushout ≪≫ HasColimit.isoOfNatIso e) (N.app (V, Y)) ?_
  apply s.hom_ext
  · change F.map (pushout.inl (i ▷ X) (U ◁ j)) ≫
      (s.isoPushout.hom ≫ (HasColimit.isoOfNatIso e).hom) ≫
        pushout.desc (F.obj V ◁ F.map j) (F.map i ▷ F.obj Y) _ =
      F.map (pushout.inl (i ▷ X) (U ◁ j)) ≫ F.map (pushout.desc (V ◁ j) (i ▷ Y) _) ≫ (N.app (V, Y)).hom
    rw [Category.assoc, s.inl_isoPushout_hom_assoc]
    rw [← Category.assoc, hcolLeft, Category.assoc]
    conv_rhs => rw [← Category.assoc, ← F.map_comp]
    change (N.app (V, X)).hom ≫ pushout.inl _ _ ≫
      pushout.desc (F.obj V ◁ F.map j) (F.map i ▷ F.obj Y) _ =
      F.map (pushout.inl _ _ ≫ pushout.desc (V ◁ j) (i ▷ Y) _) ≫ (N.app (V, Y)).hom
    rw [pushout.inl_desc, pushout.inl_desc]
    exact (hright j).symm
  · change F.map (pushout.inr (i ▷ X) (U ◁ j)) ≫
      (s.isoPushout.hom ≫ (HasColimit.isoOfNatIso e).hom) ≫
        pushout.desc (F.obj V ◁ F.map j) (F.map i ▷ F.obj Y) _ =
      F.map (pushout.inr (i ▷ X) (U ◁ j)) ≫ F.map (pushout.desc (V ◁ j) (i ▷ Y) _) ≫ (N.app (V, Y)).hom
    rw [Category.assoc, s.inr_isoPushout_hom_assoc]
    rw [← Category.assoc, hcolRight, Category.assoc]
    conv_rhs => rw [← Category.assoc, ← F.map_comp]
    change (N.app (U, Y)).hom ≫ pushout.inr _ _ ≫
      pushout.desc (F.obj V ◁ F.map j) (F.map i ▷ F.obj Y) _ =
      F.map (pushout.inr _ _ ≫ pushout.desc (V ◁ j) (i ▷ Y) _) ≫ (N.app (V, Y)).hom
    rw [pushout.inr_desc, pushout.inr_desc]
    exact (hleft i).symm


end CategoryTheory.Mod.FreePushoutProducts
