/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenNatIso
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageReindexWaldhausenExact

/-!
# Natural transformations on the original general Waldhausen stages

The original postwhiskered transformation lifts through the same fully
faithful stage inclusion as the existing stage natural isomorphism API.
Its full diagram transports, every original component, and arbitrary
simplex reindexing retain all four source/target universe roles.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD

namespace CategoryTheory.Functor.IsWaldhausenExact

open Waldhausen.SConstruction

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F G K : C ⥤ D}

private def originalStagePostcomposeNatTrans
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G) (n : ℕ) :
    hF.mapStage n ⋙ Waldhausen.SConstruction.forget D n ⟶
      hG.mapStage n ⋙ Waldhausen.SConstruction.forget D n :=
  eqToHom (hF.mapStage_forget n) ≫
    Functor.whiskerLeft (Waldhausen.SConstruction.forget C n)
      ((Functor.whiskeringRight (Ar n) C D).map η) ≫
        eqToHom (hG.mapStage_forget n).symm

/-- The original natural transformation on the same two original stage functors. -/
def mapStageNatTrans (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)
    (η : F ⟶ G) (n : ℕ) : hF.mapStage n ⟶ hG.mapStage n :=
  ((fullyFaithfulForget D n).whiskeringRight (Stage C n)).preimage
    (originalStagePostcomposeNatTrans hF hG η n)

/-- The entire lifted map retains both earned whole-diagram transports
and the full original postwhiskered transformation. -/
theorem mapStageNatTrans_forget
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G) (n : ℕ) :
    Functor.whiskerRight (hF.mapStageNatTrans hG η n)
        (Waldhausen.SConstruction.forget D n) =
      eqToHom (hF.mapStage_forget n) ≫
        Functor.whiskerLeft (Waldhausen.SConstruction.forget C n)
          ((Functor.whiskeringRight (Ar n) C D).map η) ≫
            eqToHom (hG.mapStage_forget n).symm :=
  ((fullyFaithfulForget D n).whiskeringRight (Stage C n)).map_preimage
    (originalStagePostcomposeNatTrans hF hG η n)

private def computedStageNatTrans
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G) (n : ℕ) :
    hF.mapStage n ⟶ hG.mapStage n where
  app A := ObjectProperty.homMk (Functor.whiskerLeft A.obj η)
  naturality A B φ := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext x
    exact η.naturality (φ.hom.app x)

private theorem computedStageNatTrans_forget
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G) (n : ℕ) :
    Functor.whiskerRight (computedStageNatTrans hF hG η n)
        (Waldhausen.SConstruction.forget D n) =
      originalStagePostcomposeNatTrans hF hG η n := by
  apply NatTrans.ext
  funext A
  simp only [originalStagePostcomposeNatTrans, NatTrans.comp_app, eqToHom_app]
  exact (conj_eqToHom_iff_heq
    ((Functor.whiskerRight (computedStageNatTrans hF hG η n)
      (Waldhausen.SConstruction.forget D n)).app A)
    (Functor.whiskerLeft A.obj η) (hF.mapStage_obj n A) (hG.mapStage_obj n A)).mpr
      (by rfl)

private theorem mapStageNatTrans_eq_computed
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G) (n : ℕ) :
    hF.mapStageNatTrans hG η n = computedStageNatTrans hF hG η n := by
  apply ((fullyFaithfulForget D n).whiskeringRight (Stage C n)).map_injective
  exact (mapStageNatTrans_forget hF hG η n).trans
    (computedStageNatTrans_forget hF hG η n).symm

/-- The whole stage arrow is the literal original transformation whiskered
by the original flag diagram. -/
theorem mapStageNatTrans_app_hom
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G) (n : ℕ)
    (A : Stage C n) :
    ((hF.mapStageNatTrans hG η n).app A).hom = Functor.whiskerLeft A.obj η := by
  rw [mapStageNatTrans_eq_computed]
  rfl

/-- Every original interval retains its original natural-transformation component. -/
theorem mapStageNatTrans_app_hom_app
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G) (n : ℕ)
    (A : Stage C n) (x : Ar n) :
    ((hF.mapStageNatTrans hG η n).app A).hom.app x = η.app (A.obj.obj x) := by
  rw [mapStageNatTrans_app_hom]
  rfl

/-- Identity transformations retain the whole original stage identity. -/
theorem mapStageNatTrans_id (hF : F.IsWaldhausenExact) (n : ℕ) :
    hF.mapStageNatTrans hF (𝟙 F) n = 𝟙 (hF.mapStage n) := by
  apply NatTrans.ext
  funext A
  apply ObjectProperty.hom_ext
  rw [mapStageNatTrans_app_hom]
  rfl

/-- The complete original stage transformation respects composition. -/
theorem mapStageNatTrans_comp (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)
    (hK : K.IsWaldhausenExact) (η : F ⟶ G) (κ : G ⟶ K) (n : ℕ) :
    hF.mapStageNatTrans hK (η ≫ κ) n =
      hF.mapStageNatTrans hG η n ≫ hG.mapStageNatTrans hK κ n := by
  apply NatTrans.ext
  funext A
  apply ObjectProperty.hom_ext
  rw [NatTrans.comp_app]
  change ((hF.mapStageNatTrans hK (η ≫ κ) n).app A).hom =
    ((hF.mapStageNatTrans hG η n).app A).hom ≫
      ((hG.mapStageNatTrans hK κ n).app A).hom
  rw [mapStageNatTrans_app_hom, mapStageNatTrans_app_hom, mapStageNatTrans_app_hom]
  rfl

private theorem natTransHExt
    {A B : Type*} [Category A] [Category B] {L M L' M' : A ⥤ B}
    (hL : L = L') (hM : M = M') (α : L ⟶ M) (β : L' ⟶ M')
    (h : ∀ X : A, HEq (α.app X) (β.app X)) : HEq α β := by
  cases hL
  cases hM
  apply heq_of_eq
  apply NatTrans.ext
  funext X
  exact eq_of_heq (h X)

private theorem stageHomHEq {n : ℕ} {A B A' B' : Stage D n}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : HEq f.hom g.hom) : HEq f g := by
  cases hA
  cases hB
  apply heq_of_eq
  apply ObjectProperty.hom_ext
  exact eq_of_heq h

/-- Every original simplex operator retains the complete original
transformation, with its independently computed endpoint diagrams. -/
theorem mapStageNatTrans_app_reindex_hom
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G)
    {a b : SimplexCategory} (f : a ⟶ b) (A : Stage C b.len) :
    HEq (((reindexStage (C := D) f).map ((hF.mapStageNatTrans hG η b.len).app A)).hom)
      (((hF.mapStageNatTrans hG η a.len).app ((reindexStage (C := C) f).obj A)).hom) := by
  rw [mapStageNatTrans_eq_computed, mapStageNatTrans_eq_computed]
  rfl

/-- The whole stage transformation commutes with all original reindex functors,
using the same original exact-stage functor equalities. -/
theorem mapStageNatTrans_reindex
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G)
    {a b : SimplexCategory} (f : a ⟶ b) :
    HEq (Functor.whiskerLeft (reindexStage (C := C) f)
      (hF.mapStageNatTrans hG η a.len))
      (Functor.whiskerRight (hF.mapStageNatTrans hG η b.len) (reindexStage (C := D) f)) := by
  apply natTransHExt (hF.mapStage_reindex f) (hG.mapStage_reindex f)
  intro A
  exact stageHomHEq (Functor.congr_obj (hF.mapStage_reindex f) A)
    (Functor.congr_obj (hG.mapStage_reindex f) A)
    _ _ (mapStageNatTrans_app_reindex_hom hF hG η f A).symm

end CategoryTheory.Functor.IsWaldhausenExact

end
