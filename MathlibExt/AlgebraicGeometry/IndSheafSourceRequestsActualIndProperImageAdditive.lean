/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels
import Mathlib.CategoryTheory.Limits.Indization.Category
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Topology.Sheaves.Functors

/-!
# Additivity of the actual ind-sheaf proper direct image

The prescribed compact-Yoneda left Kan extension of compact-support pushforward
is additive.

Source: D'Agnolo--Kashiwara1311.2374v2, Sections2.2/3.2/3.3;
Kashiwara--Schapira, Ind-sheaves.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.IndSheafSourceRequests

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
open MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels

private instance compactPushforwardAdditive (k : Type) [Field k] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (P : CompactPushforwardSource k f)
    [CompactSheafSource k X] [CompactSheafSource k Y] :
    (compactPushforward k f P).Additive where
  map_add {F G a b} := by
    have hpush : (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).Additive :=
      preservesFiniteLimits_le_additiveFunctor _ _ _ inferInstance
    apply ObjectProperty.hom_ext
    change (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).map (a + b).hom = _
    exact hpush.map_add.trans rfl

private instance indYonedaAdditive (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] :
    (Ind.yoneda (C := CompactSheaf k X)).Additive :=
  preservesFiniteColimits_le_additiveFunctor _ _ _ inferInstance

private theorem indCommaFinallySmall {C : Type*} [Category.{0} C] (A : Ind C) :
    FinallySmall.{0} (CostructuredArrow Ind.yoneda A) := by
  let e := ((CostructuredArrow.post Ind.yoneda (Ind.inclusion C) A).asEquivalence.trans
    (CostructuredArrow.mapNatIso Ind.yonedaCompInclusion))
  have := (Ind.isIndObject_inclusion_obj A).finallySmall
  exact finallySmall_of_final_of_finallySmall e.inverse

private theorem indPointwise {C H : Type*} [Category.{0} C] [Category H]
    [HasColimitsOfSize.{0, 0} H] (F : C ⥤ H) :
    (Ind.yoneda (C := C)).HasPointwiseLeftKanExtension F := by
  intro A
  have := indCommaFinallySmall A
  have := hasColimitsOfShape_of_finallySmall (CostructuredArrow Ind.yoneda A) H
  infer_instance

private theorem extensionUnit_map_add {C B H : Type*}
    [Category C] [Category B] [Category H]
    [Preadditive C] [Preadditive B] [Preadditive H] [HasBinaryBiproducts C]
    (L : C ⥤ B) (F : C ⥤ H) [L.Additive] [F.Additive]
    (G : B ⥤ H) (α : F ⟶ L ⋙ G) (c : C) {b : B} (u v : L.obj c ⟶ b) :
    α.app c ≫ G.map (u + v) = α.app c ≫ G.map u + α.app c ≫ G.map v := by
  let w : L.obj (c ⊞ c) ⟶ b := L.map biprod.fst ≫ u + L.map biprod.snd ≫ v
  have hi : L.map (biprod.inl : c ⟶ c ⊞ c) ≫ w = u := by
    simp [w, Preadditive.comp_add, ← L.map_comp, ← Category.assoc]
  have hj : L.map (biprod.inr : c ⟶ c ⊞ c) ≫ w = v := by
    simp [w, Preadditive.comp_add, ← L.map_comp, ← Category.assoc]
  have hd : L.map ((biprod.inl : c ⟶ c ⊞ c) + biprod.inr) ≫ w = u + v := by
    rw [L.map_add, Preadditive.add_comp, hi, hj]
  have hn (t : c ⟶ c ⊞ c) :
      (F.map t ≫ α.app (c ⊞ c)) ≫ G.map w = α.app c ≫ G.map (L.map t ≫ w) := by
    rw [α.naturality]
    change (α.app c ≫ G.map (L.map t)) ≫ G.map w = _
    rw [Category.assoc, ← G.map_comp]
  rw [← hd, G.map_comp, ← Category.assoc]
  change (α.app c ≫ (L ⋙ G).map
    ((biprod.inl : c ⟶ c ⊞ c) + biprod.inr)) ≫ G.map w = _
  rw [← α.naturality]
  rw [F.map_add, Preadditive.add_comp, Preadditive.add_comp]
  rw [hn, hn, hi, hj]

private theorem pointwiseAdditive {C B H : Type*}
    [Category C] [Category B] [Category H]
    [Preadditive C] [Preadditive B] [Preadditive H] [HasBinaryBiproducts C]
    (L : C ⥤ B) (F : C ⥤ H) [L.Additive] [F.Additive]
    (G : B ⥤ H) (α : F ⟶ L ⋙ G)
    (h : (Functor.LeftExtension.mk G α).IsPointwiseLeftKanExtension) : G.Additive where
  map_add {A B a b} := by
    apply (h A).hom_ext'
    intro c φ
    change α.app c ≫ G.map φ ≫ G.map (a + b) =
      α.app c ≫ G.map φ ≫ (G.map a + G.map b)
    simpa only [Preadditive.comp_add, ← G.map_comp] using
      extensionUnit_map_add L F G α c (φ ≫ a) (φ ≫ b)

/-- The native compact-generator extension has its ordinary additive structure. -/
theorem actual_ind_proper_image_additive (k : Type) [Field k]
    (X Y : TopCat.{0}) [CompactSheafSource k X] [CompactSheafSource k Y]
    (f : X ⟶ Y) (P : CompactPushforwardSource k f) (D : IndPushforwardSource k f P) :
    (indProperImage k f P D).Additive := by
  let := D.hasKan
  let := indPointwise (compactPushforward k f P ⋙ Ind.yoneda)
  have : (indProperImage k f P D).IsLeftKanExtension (compactPushforwardUnit k f P D) := by
    dsimp [indProperImage, compactPushforwardUnit]
    infer_instance
  exact pointwiseAdditive Ind.yoneda (compactPushforward k f P ⋙ Ind.yoneda)
    (indProperImage k f P D) (compactPushforwardUnit k f P D)
    (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ _)

end WantedExt.AlgebraicGeometry.IndSheafSourceRequests
