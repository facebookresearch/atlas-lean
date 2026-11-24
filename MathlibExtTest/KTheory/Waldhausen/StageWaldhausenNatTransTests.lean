/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenNatTrans

/-!
# Clients for the original four-role stage natural transformation

The whole postwhiskered map, its original component formula, and arbitrary
simplex reindexing use independently specified source and target categories.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD

namespace MathlibExtTest.KTheory.Waldhausen.StageWaldhausenNatTransTests

open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SConstruction

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F G K : C ⥤ D}

/-- The complete stage map retains both original stage-forget transports. -/
theorem originalWholeWhiskering (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)
    (η : F ⟶ G) (n : ℕ) :
    Functor.whiskerRight (hF.mapStageNatTrans hG η n) (SConstruction.forget D n) =
      eqToHom (hF.mapStage_forget n) ≫
        Functor.whiskerLeft (SConstruction.forget C n)
          ((Functor.whiskeringRight (Ar n) C D).map η) ≫
            eqToHom (hG.mapStage_forget n).symm :=
  Functor.IsWaldhausenExact.mapStageNatTrans_forget hF hG η n

/-- The full original flag diagram acts on the original transformation. -/
theorem originalWholeStageArrow (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)
    (η : F ⟶ G) (n : ℕ) (A : Stage C n) :
    ((hF.mapStageNatTrans hG η n).app A).hom = Functor.whiskerLeft A.obj η :=
  Functor.IsWaldhausenExact.mapStageNatTrans_app_hom hF hG η n A

/-- Every scalar interval component is the original scalar component. -/
theorem originalIntervalComponent (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)
    (η : F ⟶ G) (n : ℕ) (A : Stage C n) (x : Ar n) :
    ((hF.mapStageNatTrans hG η n).app A).hom.app x = η.app (A.obj.obj x) :=
  Functor.IsWaldhausenExact.mapStageNatTrans_app_hom_app hF hG η n A x

/-- Both actual source and target universe roles are preserved under every reindex. -/
theorem originalEveryReindex (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)
    (η : F ⟶ G) {a b : SimplexCategory} (f : a ⟶ b) :
    HEq (Functor.whiskerLeft (reindexStage (C := C) f)
      (hF.mapStageNatTrans hG η a.len))
      (Functor.whiskerRight (hF.mapStageNatTrans hG η b.len) (reindexStage (C := D) f)) :=
  Functor.IsWaldhausenExact.mapStageNatTrans_reindex hF hG η f

/-- The actual two-arrow stage transformation retains composition. -/
theorem originalComposition (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)
    (hK : K.IsWaldhausenExact) (η : F ⟶ G) (κ : G ⟶ K) (n : ℕ) :
    hF.mapStageNatTrans hK (η ≫ κ) n =
      hF.mapStageNatTrans hG η n ≫ hG.mapStageNatTrans hK κ n :=
  Functor.IsWaldhausenExact.mapStageNatTrans_comp hF hG hK η κ n

/-- Degree zero uses the same full stage transformation on the original zero stages. -/
theorem originalDegreeZero (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)
    (η : F ⟶ G) (A : Stage C 0) (x : Ar 0) :
    ((hF.mapStageNatTrans hG η 0).app A).hom.app x = η.app (A.obj.obj x) :=
  Functor.IsWaldhausenExact.mapStageNatTrans_app_hom_app hF hG η 0 A x

end MathlibExtTest.KTheory.Waldhausen.StageWaldhausenNatTransTests

end
