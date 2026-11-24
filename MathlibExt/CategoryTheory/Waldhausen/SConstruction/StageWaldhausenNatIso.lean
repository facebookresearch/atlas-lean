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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenFunctoriality
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Whiskering

/-!
# Actual natural isomorphisms on generic Waldhausen stages

The SAME generic stage maps lift the original postcomposition Iso through
their SAME fully faithful forgetful functors. Both whole hom and inverse
map formulas retain the actual object transports. The same natural Iso
restricts in both directions to the original pointwise weak-stage category.
Source and target object/Hom universes remain independent.
-/

public section

noncomputable section

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor.IsWaldhausenExact

open Waldhausen.SConstruction

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F G : C ⥤ D}

/-- The WHOLE original stage map followed by original forgetting is the
original diagram followed by the SAME whole postcomposition functor. -/
theorem mapStage_forget (hF : F.IsWaldhausenExact) (n : ℕ) :
    hF.mapStage n ⋙ Waldhausen.SConstruction.forget D n =
      Waldhausen.SConstruction.forget C n ⋙
        (Functor.whiskeringRight (Ar n) C D).obj F := by
  apply Functor.hext
  · intro X
    exact hF.mapStage_obj n X
  · intro X Y f
    exact heq_of_eq (hF.mapStage_map n f)

private def originalStagePostcomposeIso
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (e : F ≅ G) (n : ℕ) :
    hF.mapStage n ⋙ Waldhausen.SConstruction.forget D n ≅
      hG.mapStage n ⋙ Waldhausen.SConstruction.forget D n :=
  (eqToIso (hF.mapStage_forget n)) ≪≫
    (Functor.isoWhiskerLeft (Waldhausen.SConstruction.forget C n)
      ((Functor.whiskeringRight (Ar n) C D).mapIso e)) ≪≫
    (eqToIso (hG.mapStage_forget n)).symm

/-- The original natural Iso lifts through the SAME fully faithful original
stage inclusion to the SAME hF/hG stage functors, in every finite degree. -/
def mapStageNatIso (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)
    (e : F ≅ G) (n : ℕ) : hF.mapStage n ≅ hG.mapStage n :=
  ((fullyFaithfulForget D n).whiskeringRight (Stage C n)).preimageIso
    (originalStagePostcomposeIso hF hG e n)

private theorem mapStageNatIso_hom_forget_aux
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (e : F ≅ G) (n : ℕ) :
    Functor.whiskerRight (hF.mapStageNatIso hG e n).hom
        (Waldhausen.SConstruction.forget D n) =
      (originalStagePostcomposeIso hF hG e n).hom := by
  exact ((fullyFaithfulForget D n).whiskeringRight (Stage C n)).map_preimage
    (originalStagePostcomposeIso hF hG e n).hom

/-- The ENTIRE original forward natural transformation keeps both WHOLE
stage-forget transports and the SAME original e.hom in every diagram/map. -/
theorem mapStageNatIso_hom_forget
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (e : F ≅ G) (n : ℕ) :
    Functor.whiskerRight (hF.mapStageNatIso hG e n).hom
        (Waldhausen.SConstruction.forget D n) =
      eqToHom (hF.mapStage_forget n) ≫
        Functor.whiskerLeft (Waldhausen.SConstruction.forget C n)
          ((Functor.whiskeringRight (Ar n) C D).map e.hom) ≫
        eqToHom (hG.mapStage_forget n).symm := by
  simpa only [originalStagePostcomposeIso, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom, eqToIso.inv, Functor.isoWhiskerLeft_hom, Functor.mapIso_hom,
    Category.assoc] using mapStageNatIso_hom_forget_aux hF hG e n

private theorem mapStageNatIso_inv_forget_aux
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (e : F ≅ G) (n : ℕ) :
    Functor.whiskerRight (hF.mapStageNatIso hG e n).inv
        (Waldhausen.SConstruction.forget D n) =
      (originalStagePostcomposeIso hF hG e n).inv := by
  exact ((fullyFaithfulForget D n).whiskeringRight (Stage C n)).map_preimage
    (originalStagePostcomposeIso hF hG e n).inv

/-- The ENTIRE original inverse natural transformation keeps both WHOLE
stage-forget transports and the SAME original e.inv in every diagram/map. -/
theorem mapStageNatIso_inv_forget
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (e : F ≅ G) (n : ℕ) :
    Functor.whiskerRight (hF.mapStageNatIso hG e n).inv
        (Waldhausen.SConstruction.forget D n) =
      eqToHom (hG.mapStage_forget n) ≫
        Functor.whiskerLeft (Waldhausen.SConstruction.forget C n)
          ((Functor.whiskeringRight (Ar n) C D).map e.inv) ≫
        eqToHom (hF.mapStage_forget n).symm := by
  simpa only [originalStagePostcomposeIso, Iso.trans_inv, Iso.symm_inv,
    eqToIso.hom, eqToIso.inv, Functor.isoWhiskerLeft_inv, Functor.mapIso_inv,
    Category.assoc] using mapStageNatIso_inv_forget_aux hF hG e n

private def originalWeakStagePostcomposeIso
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (e : F ≅ G) (n : ℕ) :
    hF.mapStageWeak n ⋙ stageWeakInclusion D n ≅
      hG.mapStageWeak n ⋙ stageWeakInclusion D n :=
  (eqToIso (hF.mapStageWeak_inclusion n)) ≪≫
    (Functor.isoWhiskerLeft (stageWeakInclusion C n) (hF.mapStageNatIso hG e n)) ≪≫
    (eqToIso (hG.mapStageWeak_inclusion n)).symm

/-- The SAME actual natural Iso restricts in BOTH directions through the
original weak inclusion, using the original IsIso weak property. -/
def mapStageWeakNatIso (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)
    (e : F ≅ G) (n : ℕ) : hF.mapStageWeak n ≅ hG.mapStageWeak n := by
  let s := originalWeakStagePostcomposeIso hF hG e n
  refine NatIso.ofComponents (fun X =>
    WideSubcategory.isoMk (s.app X)
      ((stageWeak D n).of_isIso (s.app X).hom)
      ((stageWeak D n).of_isIso (s.app X).inv)) ?_
  intro X Y f
  apply WideSubcategory.hom_ext
  exact s.hom.naturality f

private theorem mapStageWeakNatIso_hom_inclusion_aux
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (e : F ≅ G) (n : ℕ) :
    Functor.whiskerRight (hF.mapStageWeakNatIso hG e n).hom (stageWeakInclusion D n) =
      (originalWeakStagePostcomposeIso hF hG e n).hom := by
  rfl

/-- The WHOLE original weak-stage hom, after SAME inclusion, is the SAME
stage hom through BOTH actual weak-stage inclusion functor transports. -/
theorem mapStageWeakNatIso_hom_inclusion
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (e : F ≅ G) (n : ℕ) :
    Functor.whiskerRight (hF.mapStageWeakNatIso hG e n).hom (stageWeakInclusion D n) =
      eqToHom (hF.mapStageWeak_inclusion n) ≫
        Functor.whiskerLeft (stageWeakInclusion C n) (hF.mapStageNatIso hG e n).hom ≫
        eqToHom (hG.mapStageWeak_inclusion n).symm := by
  simpa only [originalWeakStagePostcomposeIso, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom, eqToIso.inv, Functor.isoWhiskerLeft_hom, Category.assoc] using
    mapStageWeakNatIso_hom_inclusion_aux hF hG e n

private theorem mapStageWeakNatIso_inv_inclusion_aux
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (e : F ≅ G) (n : ℕ) :
    Functor.whiskerRight (hF.mapStageWeakNatIso hG e n).inv (stageWeakInclusion D n) =
      (originalWeakStagePostcomposeIso hF hG e n).inv := by
  rfl

/-- The WHOLE original weak-stage inv, after SAME inclusion, is the SAME
stage inv through BOTH actual weak-stage inclusion functor transports. -/
theorem mapStageWeakNatIso_inv_inclusion
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (e : F ≅ G) (n : ℕ) :
    Functor.whiskerRight (hF.mapStageWeakNatIso hG e n).inv (stageWeakInclusion D n) =
      eqToHom (hG.mapStageWeak_inclusion n) ≫
        Functor.whiskerLeft (stageWeakInclusion C n) (hF.mapStageNatIso hG e n).inv ≫
        eqToHom (hF.mapStageWeak_inclusion n).symm := by
  simpa only [originalWeakStagePostcomposeIso, Iso.trans_inv, Iso.symm_inv,
    eqToIso.hom, eqToIso.inv, Functor.isoWhiskerLeft_inv, Category.assoc] using
    mapStageWeakNatIso_inv_inclusion_aux hF hG e n

end CategoryTheory.Functor.IsWaldhausenExact

end
