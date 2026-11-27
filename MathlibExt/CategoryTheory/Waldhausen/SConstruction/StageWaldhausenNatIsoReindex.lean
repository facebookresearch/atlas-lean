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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenNatIso

/-!
# Reindex compatibility of the original Waldhausen Stage natural isomorphisms

Both original components commute with reindexing through the original two
functor transports. Forgetting the Stage structures computes each component
from the original natural isomorphism. The original weak inclusions retain
these same components. Source and target object and morphism universes remain
independent; no original functor or natural-isomorphism value is replaced.
-/

public section

noncomputable section

open CategoryTheory Limits

universe vC uC vD uD

namespace CategoryTheory.Functor.IsWaldhausenExact

open Waldhausen.SConstruction

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F G : C ⥤ D}

private theorem originalStageReindexObjComponentValue
    (C : Type uC) [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
    {a b : SimplexCategory} (f : a ⟶ b) (X : Stage C b.len) (k : Ar a.len) :
    ((reindexStage (C := C) f).obj X).obj.obj k =
      X.obj.obj ((indexFunctor f).obj k) := by
  rfl

private theorem originalStageReindexMapComponentValue
    (C : Type uC) [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
    {a b : SimplexCategory} (f : a ⟶ b)
    {X Y : Stage C b.len} (eta : X ⟶ Y) (k : Ar a.len) :
    ((reindexStage (C := C) f).map eta).hom.app k =
      eta.hom.app ((indexFunctor f).obj k) := by
  rfl

private theorem originalStageNatIsoHomComponentHEq
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (e : F ≅ G)
    (n : ℕ) (X : Stage C n) (k : Ar n) :
    HEq (((hF.mapStageNatIso hG e n).hom.app X).hom.app k)
      (e.hom.app (X.obj.obj k)) := by
  have hApp : ((hF.mapStageNatIso hG e n).hom.app X).hom.app k =
      eqToHom (Functor.congr_obj (hF.mapStage_obj n X) k) ≫
        e.hom.app (X.obj.obj k) ≫
        eqToHom (Functor.congr_obj (hG.mapStage_obj n X) k).symm := by
    have h := congrArg (fun η => (η.app X).app k)
      (hF.mapStageNatIso_hom_forget hG e n)
    rw [Functor.whiskerRight_app] at h
    have hForget :
        ((forget D n).map ((hF.mapStageNatIso hG e n).hom.app X)).app k =
          ((hF.mapStageNatIso hG e n).hom.app X).hom.app k := by
      exact congrArg (fun η => η.app k)
        (ObjectProperty.ι_map (P := stageProperty D n)
          (f := (hF.mapStageNatIso hG e n).hom.app X))
    rw [hForget] at h
    have hMiddle :
        ((Functor.whiskerLeft (forget C n)
          ((Functor.whiskeringRight (Ar n) C D).map e.hom)).app X).app k =
            e.hom.app (X.obj.obj k) := by
      have hPoint : ((forget C n).obj X).obj k = X.obj.obj k :=
        Functor.congr_obj (ObjectProperty.ι_obj (P := stageProperty C n) (X := X)) k
      have hChange : HEq
          (e.hom.app (((forget C n).obj X).obj k))
          (e.hom.app (X.obj.obj k)) :=
        (conj_eqToHom_iff_heq _ _
          (congrArg F.obj hPoint) (congrArg G.obj hPoint)).1
            (by simpa only [eqToHom_map] using NatTrans.congr e.hom hPoint)
      rw [Functor.whiskerLeft_app, Functor.whiskeringRight_map_app_app]
      exact eq_of_heq hChange
    simp only [NatTrans.vcomp_app', eqToHom_app] at h
    rw [hMiddle] at h
    simpa only [Functor.comp_obj, Functor.whiskeringRight_obj_obj,
      ObjectProperty.ι_obj] using h
  rw [hApp]
  exact (eqToHom_comp_heq
    (e.hom.app (X.obj.obj k) ≫
      eqToHom (Functor.congr_obj (hG.mapStage_obj n X) k).symm)
    (Functor.congr_obj (hF.mapStage_obj n X) k)).trans
      (comp_eqToHom_heq (e.hom.app (X.obj.obj k))
        (Functor.congr_obj (hG.mapStage_obj n X) k).symm)

private theorem originalStageNatIsoInvComponentHEq
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (e : F ≅ G)
    (n : ℕ) (X : Stage C n) (k : Ar n) :
    HEq (((hF.mapStageNatIso hG e n).inv.app X).hom.app k)
      (e.inv.app (X.obj.obj k)) := by
  have hApp : ((hF.mapStageNatIso hG e n).inv.app X).hom.app k =
      eqToHom (Functor.congr_obj (hG.mapStage_obj n X) k) ≫
        e.inv.app (X.obj.obj k) ≫
        eqToHom (Functor.congr_obj (hF.mapStage_obj n X) k).symm := by
    have h := congrArg (fun η => (η.app X).app k)
      (hF.mapStageNatIso_inv_forget hG e n)
    rw [Functor.whiskerRight_app] at h
    have hForget :
        ((forget D n).map ((hF.mapStageNatIso hG e n).inv.app X)).app k =
          ((hF.mapStageNatIso hG e n).inv.app X).hom.app k := by
      exact congrArg (fun η => η.app k)
        (ObjectProperty.ι_map (P := stageProperty D n)
          (f := (hF.mapStageNatIso hG e n).inv.app X))
    rw [hForget] at h
    have hMiddle :
        ((Functor.whiskerLeft (forget C n)
          ((Functor.whiskeringRight (Ar n) C D).map e.inv)).app X).app k =
            e.inv.app (X.obj.obj k) := by
      have hPoint : ((forget C n).obj X).obj k = X.obj.obj k :=
        Functor.congr_obj (ObjectProperty.ι_obj (P := stageProperty C n) (X := X)) k
      have hChange : HEq
          (e.inv.app (((forget C n).obj X).obj k))
          (e.inv.app (X.obj.obj k)) :=
        (conj_eqToHom_iff_heq _ _
          (congrArg G.obj hPoint) (congrArg F.obj hPoint)).1
            (by simpa only [eqToHom_map] using NatTrans.congr e.inv hPoint)
      rw [Functor.whiskerLeft_app, Functor.whiskeringRight_map_app_app]
      exact eq_of_heq hChange
    simp only [NatTrans.vcomp_app', eqToHom_app] at h
    rw [hMiddle] at h
    simpa only [Functor.comp_obj, Functor.whiskeringRight_obj_obj,
      ObjectProperty.ι_obj] using h
  rw [hApp]
  exact (eqToHom_comp_heq
    (e.inv.app (X.obj.obj k) ≫
      eqToHom (Functor.congr_obj (hF.mapStage_obj n X) k).symm)
    (Functor.congr_obj (hG.mapStage_obj n X) k)).trans
      (comp_eqToHom_heq (e.inv.app (X.obj.obj k))
        (Functor.congr_obj (hF.mapStage_obj n X) k).symm)

/-- The whole original Stage hom commutes with reindexing through both original transports. -/
theorem mapStageNatIso_hom_reindex
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (e : F ≅ G)
    {a b : SimplexCategory} (f : a ⟶ b) :
    Functor.whiskerLeft (reindexStage (C := C) f)
        (hF.mapStageNatIso hG e a.len).hom =
      eqToHom (hF.mapStage_reindex f) ≫
        Functor.whiskerRight (hF.mapStageNatIso hG e b.len).hom
          (reindexStage (C := D) f) ≫
        eqToHom (hG.mapStage_reindex f).symm := by
  apply ((fullyFaithfulForget D a.len).whiskeringRight (Stage C b.len)).map_injective
  apply NatTrans.ext
  funext X
  apply NatTrans.ext
  funext k
  change (((hF.mapStageNatIso hG e a.len).hom.app
      ((reindexStage (C := C) f).obj X)).hom.app k) =
    ((forget D a.len).map
      ((eqToHom (hF.mapStage_reindex f)).app X ≫
        (reindexStage (C := D) f).map
          ((hF.mapStageNatIso hG e b.len).hom.app X) ≫
        (eqToHom (hG.mapStage_reindex f).symm).app X)).app k
  simp only [Functor.map_comp, eqToHom_app, eqToHom_map]
  let tF := congrArg (fun A : Stage D a.len => A.obj.obj k)
    (Functor.congr_obj (hF.mapStage_reindex f) X)
  let tG := congrArg (fun A : Stage D a.len => A.obj.obj k)
    (Functor.congr_obj (hG.mapStage_reindex f) X)
  change (((hF.mapStageNatIso hG e a.len).hom.app
      ((reindexStage (C := C) f).obj X)).hom.app k) =
    eqToHom tF ≫
      ((reindexStage (C := D) f).map
        ((hF.mapStageNatIso hG e b.len).hom.app X)).hom.app k ≫
      eqToHom tG.symm
  let Y := X.obj.obj ((indexFunctor f).obj k)
  have hObj := originalStageReindexObjComponentValue C f X k
  have hMove : HEq
      (e.hom.app (((reindexStage (C := C) f).obj X).obj.obj k))
      (e.hom.app Y) :=
    (conj_eqToHom_iff_heq _ _ (congrArg F.obj hObj) (congrArg G.obj hObj)).1
      (by simpa only [eqToHom_map] using NatTrans.congr e.hom hObj)
  have hLeft := (originalStageNatIsoHomComponentHEq hF hG e a.len
    ((reindexStage (C := C) f).obj X) k).trans hMove
  have hCore : HEq
      (((reindexStage (C := D) f).map
        ((hF.mapStageNatIso hG e b.len).hom.app X)).hom.app k)
      (e.hom.app Y) := by
    rw [originalStageReindexMapComponentValue D f]
    exact originalStageNatIsoHomComponentHEq hF hG e b.len X ((indexFunctor f).obj k)
  have hRight := (eqToHom_comp_heq
    (((reindexStage (C := D) f).map
      ((hF.mapStageNatIso hG e b.len).hom.app X)).hom.app k ≫ eqToHom tG.symm) tF).trans
      ((comp_eqToHom_heq
        (((reindexStage (C := D) f).map
          ((hF.mapStageNatIso hG e b.len).hom.app X)).hom.app k) tG.symm).trans hCore)
  exact eq_of_heq (hLeft.trans hRight.symm)

/-- The whole original Stage inverse commutes with reindexing through both original transports. -/
theorem mapStageNatIso_inv_reindex
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (e : F ≅ G)
    {a b : SimplexCategory} (f : a ⟶ b) :
    Functor.whiskerLeft (reindexStage (C := C) f)
        (hF.mapStageNatIso hG e a.len).inv =
      eqToHom (hG.mapStage_reindex f) ≫
        Functor.whiskerRight (hF.mapStageNatIso hG e b.len).inv
          (reindexStage (C := D) f) ≫
        eqToHom (hF.mapStage_reindex f).symm := by
  apply ((fullyFaithfulForget D a.len).whiskeringRight (Stage C b.len)).map_injective
  apply NatTrans.ext
  funext X
  apply NatTrans.ext
  funext k
  change (((hF.mapStageNatIso hG e a.len).inv.app
      ((reindexStage (C := C) f).obj X)).hom.app k) =
    ((forget D a.len).map
      ((eqToHom (hG.mapStage_reindex f)).app X ≫
        (reindexStage (C := D) f).map
          ((hF.mapStageNatIso hG e b.len).inv.app X) ≫
        (eqToHom (hF.mapStage_reindex f).symm).app X)).app k
  simp only [Functor.map_comp, eqToHom_app, eqToHom_map]
  let tG := congrArg (fun A : Stage D a.len => A.obj.obj k)
    (Functor.congr_obj (hG.mapStage_reindex f) X)
  let tF := congrArg (fun A : Stage D a.len => A.obj.obj k)
    (Functor.congr_obj (hF.mapStage_reindex f) X)
  change (((hF.mapStageNatIso hG e a.len).inv.app
      ((reindexStage (C := C) f).obj X)).hom.app k) =
    eqToHom tG ≫
      ((reindexStage (C := D) f).map
        ((hF.mapStageNatIso hG e b.len).inv.app X)).hom.app k ≫
      eqToHom tF.symm
  let Y := X.obj.obj ((indexFunctor f).obj k)
  have hObj := originalStageReindexObjComponentValue C f X k
  have hMove : HEq
      (e.inv.app (((reindexStage (C := C) f).obj X).obj.obj k))
      (e.inv.app Y) :=
    (conj_eqToHom_iff_heq _ _ (congrArg G.obj hObj) (congrArg F.obj hObj)).1
      (by simpa only [eqToHom_map] using NatTrans.congr e.inv hObj)
  have hLeft := (originalStageNatIsoInvComponentHEq hF hG e a.len
    ((reindexStage (C := C) f).obj X) k).trans hMove
  have hCore : HEq
      (((reindexStage (C := D) f).map
        ((hF.mapStageNatIso hG e b.len).inv.app X)).hom.app k)
      (e.inv.app Y) := by
    rw [originalStageReindexMapComponentValue D f]
    exact originalStageNatIsoInvComponentHEq hF hG e b.len X ((indexFunctor f).obj k)
  have hRight := (eqToHom_comp_heq
    (((reindexStage (C := D) f).map
      ((hF.mapStageNatIso hG e b.len).inv.app X)).hom.app k ≫ eqToHom tF.symm) tG).trans
      ((comp_eqToHom_heq
        (((reindexStage (C := D) f).map
          ((hF.mapStageNatIso hG e b.len).inv.app X)).hom.app k) tF.symm).trans hCore)
  exact eq_of_heq (hLeft.trans hRight.symm)

end CategoryTheory.Functor.IsWaldhausenExact

end
