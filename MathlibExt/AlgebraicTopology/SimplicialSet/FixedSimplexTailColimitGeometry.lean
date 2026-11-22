/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FixedSimplexTail
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceSequentialMono

/-!
# Colimits of fixed-base pullback families along sequence tails

For sequences of simplicial sets with colimiting cocones and a commuting map between their cocone points, a fixed map into a sequence stage defines a colimiting tail pullback family. Its colimit is isomorphic to the pullback of the cocone-point map along the fixed map followed by the stage leg, with forward equations at every tail stage and inverse equations for both aggregate projections.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet.RezkFixedSimplexTail
open RezkTailPullbackColimit SharpComparisonDraft

/-- The original tail cocone, as a cocone over the SAME finite base Y_n. -/
def overCocone {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m) :
    Cocone (tailOver p n) where
  pt := Over.mk (pullback.snd q (cY.ι.app n))
  ι :=
    { app := fun k => Over.homMk ((tailPullbackCocone p n cX cY q hq).ι.app k)
        (tailPullbackCocone_legs p n cX cY q hq k).2
      naturality := by
        intro i j f
        apply Over.OverMorphism.ext
        exact (tailPullbackCocone p n cX cY q hq).ι.naturality f }

/-- The actual cocone is colimiting by the public tail PB-colimit theorem,
then native reflection through the slice forgetful functor. -/
def overCoconeIsColimit {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m)
    (hX : IsColimit cX) (hY : IsColimit cY) :
    IsColimit (overCocone p n cX cY q hq) := by
  apply isColimitOfReflects (Over.forget (Y.obj n))
  change IsColimit (tailPullbackCocone p n cX cY q hq)
  exact tailPullbackCoconeIsColimit p n cX cY q hq hX hY

/-- Only after choosing b, pull the SAME finite-base tail cocone back along b. -/
def cocone {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m) :
    Cocone (family p n b) :=
  (Over.pullback b ⋙ Over.forget T).mapCocone (overCocone p n cX cY q hq)

/-- This actual fixed-simplex cocone is colimiting: native filtered pullback
preservation is used, and no weak-colimit callback is an input. -/
def coconeIsColimit {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m)
    (hX : IsColimit cX) (hY : IsColimit cY) :
    IsColimit (cocone p n b cX cY q hq) := by
  letI : PreservesColimitsOfShape ℕ (Over.pullback b) :=
    SharpSaturation.overPullback_preservesColimitsOfShape_of_isFiltered ℕ b
  exact isColimitOfPreserves (Over.pullback b ⋙ Over.forget T)
    (overCoconeIsColimit p n cX cY q hq hX hY)

/-- Flatten the actual final nested pullback, preserving the original global simplex b≫ιY_n. -/
def finalIso {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m) :
    (cocone p n b cX cY q hq).pt ≅ pullback q (b ≫ cY.ι.app n) :=
  SharpPullbackClosure.nestedPullbackIso q (cY.ι.app n) b

/-- The whole actual colimit-to-fixed-simplex pullback Iso, never an individual-stage inverse. -/
def colimitIso {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m)
    (hX : IsColimit cX) (hY : IsColimit cY) :
    colimit (family p n b) ≅ pullback q (b ≫ cY.ι.app n) :=
  ((colimit.isColimit _).coconePointUniqueUpToIso (coconeIsColimit p n b cX cY q hq hX hY)).trans
    (finalIso p n b cX cY q hq)

/-- Both actual forward projection equations on EVERY original tail stage. -/
theorem colimitIso_hom_projections {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m)
    (hX : IsColimit cX) (hY : IsColimit cY) (k : ℕ) :
    colimit.ι (family p n b) k ≫ (colimitIso p n b cX cY q hq hX hY).hom ≫
        pullback.fst q (b ≫ cY.ι.app n) =
      pullback.fst _ b ≫ pullback.fst (p.app (n + k))
        (Y.map (homOfLE (Nat.le_add_right n k))) ≫ cX.ι.app (n + k) ∧
    colimit.ι (family p n b) k ≫ (colimitIso p n b cX cY q hq hX hY).hom ≫
        pullback.snd q (b ≫ cY.ι.app n) = pullback.snd _ b := by
  have stage : colimit.ι (family p n b) k ≫
      ((colimit.isColimit _).coconePointUniqueUpToIso
        (coconeIsColimit p n b cX cY q hq hX hY)).hom =
      (cocone p n b cX cY q hq).ι.app k :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
      (coconeIsColimit p n b cX cY q hq hX hY) k
  let e : colimit (family p n b) ≅ pullback (pullback.snd q (cY.ι.app n)) b :=
    (colimit.isColimit _).coconePointUniqueUpToIso
      (coconeIsColimit p n b cX cY q hq hX hY)
  have stageE : colimit.ι (family p n b) k ≫ e.hom =
      (cocone p n b cX cY q hq).ι.app k := stage
  let v : pullback (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))) ⟶
      pullback q (cY.ι.app n) := (tailPullbackCocone p n cX cY q hq).ι.app k
  have hvfst : v ≫ pullback.fst q (cY.ι.app n) =
      pullback.fst (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))) ≫
        cX.ι.app (n + k) := (tailPullbackCocone_legs p n cX cY q hq k).1
  have hvsnd : v ≫ pullback.snd q (cY.ι.app n) =
      pullback.snd (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))) :=
    (tailPullbackCocone_legs p n cX cY q hq k).2
  constructor
  · change colimit.ι (family p n b) k ≫ e.hom ≫
      (SharpPullbackClosure.nestedPullbackIso q (cY.ι.app n) b).hom ≫
        pullback.fst q (b ≫ cY.ι.app n) =
      pullback.fst (pullback.snd (p.app (n + k))
        (Y.map (homOfLE (Nat.le_add_right n k)))) b ≫
          pullback.fst (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))) ≫
            cX.ι.app (n + k)
    rw [(SharpPullbackClosure.nestedPullbackIso_hom_legs q (cY.ι.app n) b).1]
    simp only [← Category.assoc, stageE]
    change (pullback.lift
      (pullback.fst (pullback.snd (p.app (n + k))
        (Y.map (homOfLE (Nat.le_add_right n k)))) b ≫ v)
      (pullback.snd (pullback.snd (p.app (n + k))
        (Y.map (homOfLE (Nat.le_add_right n k)))) b)
      (by rw [Category.assoc, hvsnd, pullback.condition]) ≫
        pullback.fst (pullback.snd q (cY.ι.app n)) b) ≫
          pullback.fst q (cY.ι.app n) = _
    rw [pullback.lift_fst, Category.assoc, hvfst]
    exact (Category.assoc _ _ _).symm
  · change colimit.ι (family p n b) k ≫ e.hom ≫
      (SharpPullbackClosure.nestedPullbackIso q (cY.ι.app n) b).hom ≫
        pullback.snd q (b ≫ cY.ι.app n) =
      pullback.snd (pullback.snd (p.app (n + k))
        (Y.map (homOfLE (Nat.le_add_right n k)))) b
    rw [(SharpPullbackClosure.nestedPullbackIso_hom_legs q (cY.ι.app n) b).2]
    simp only [← Category.assoc, stageE]
    change pullback.lift
      (pullback.fst (pullback.snd (p.app (n + k))
        (Y.map (homOfLE (Nat.le_add_right n k)))) b ≫ v)
      (pullback.snd (pullback.snd (p.app (n + k))
        (Y.map (homOfLE (Nat.le_add_right n k)))) b)
      (by rw [Category.assoc, hvsnd, pullback.condition]) ≫
        pullback.snd (pullback.snd q (cY.ι.app n)) b = _
    exact pullback.lift_snd _ _ _

/-- Genuine aggregate projection cocones; their inverse laws are not asserted
for an individual stage inclusion. -/
def firstProjectionCocone {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m) :
    Cocone (family p n b) :=
  (cocone p n b cX cY q hq).extend ((finalIso p n b cX cY q hq).hom ≫ pullback.fst _ _)

/-- The original tail cocone projected to the domain `T` of the fixed map `b`. -/
def secondProjectionCocone {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m) :
    Cocone (family p n b) :=
  (cocone p n b cX cY q hq).extend ((finalIso p n b cX cY q hq).hom ≫ pullback.snd _ _)

/-- BOTH direct inverse equations are on the true aggregate original projections. -/
theorem colimitIso_inv_projections {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m)
    (hX : IsColimit cX) (hY : IsColimit cY) :
    (colimitIso p n b cX cY q hq hX hY).inv ≫
        colimit.desc (family p n b) (firstProjectionCocone p n b cX cY q hq) =
      pullback.fst q (b ≫ cY.ι.app n) ∧
    (colimitIso p n b cX cY q hq hX hY).inv ≫
        colimit.desc (family p n b) (secondProjectionCocone p n b cX cY q hq) =
      pullback.snd q (b ≫ cY.ι.app n) := by
  let hc := coconeIsColimit p n b cX cY q hq hX hY
  constructor
  · have desc : hc.desc (firstProjectionCocone p n b cX cY q hq) =
        (finalIso p n b cX cY q hq).hom ≫ pullback.fst _ _ := by
      apply hc.hom_ext
      intro k
      simp [firstProjectionCocone]
    simp only [colimitIso, Iso.trans_inv, Category.assoc]
    change (finalIso p n b cX cY q hq).inv ≫
      ((colimit.isColimit (family p n b)).coconePointUniqueUpToIso hc).inv ≫
        (colimit.isColimit (family p n b)).desc
          (firstProjectionCocone p n b cX cY q hq) = _
    rw [IsColimit.coconePointUniqueUpToIso_inv_desc, desc]
    exact (finalIso p n b cX cY q hq).inv_hom_id_assoc _
  · have desc : hc.desc (secondProjectionCocone p n b cX cY q hq) =
        (finalIso p n b cX cY q hq).hom ≫ pullback.snd _ _ := by
      apply hc.hom_ext
      intro k
      simp [secondProjectionCocone]
    simp only [colimitIso, Iso.trans_inv, Category.assoc]
    change (finalIso p n b cX cY q hq).inv ≫
      ((colimit.isColimit (family p n b)).coconePointUniqueUpToIso hc).inv ≫
        (colimit.isColimit (family p n b)).desc
          (secondProjectionCocone p n b cX cY q hq) = _
    rw [IsColimit.coconePointUniqueUpToIso_inv_desc, desc]
    exact (finalIso p n b cX cY q hq).inv_hom_id_assoc _
end SSet.RezkFixedSimplexTail
