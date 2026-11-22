/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinderLevelSDR
import MathlibExt.CategoryTheory.Enriched.ScalarLeibniz
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Actual native mapping cylinders and arbitrary caller coproducts

The full original interval functor preserves the caller source cofan. The
universal properties of this cofan, the caller target cofan and the actual
mapping-cylinder pushout give the colimit of the original cylinders. This
identifies the coproduct retraction with the original retraction of the
coproduct arrow, whose genuine level SDR is already proved.
-/

set_option autoImplicit false
noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective.Native
open MonoidalCategory
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.EnrichedIntervalMappingCylinder.Coproducts

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  MonoidalClosed.enrichedCategorySelf PointedCGWH.EnrichedMapping.hasSmallLimits

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] {J : Type w}

/-- Every original component arrow enters the whole caller coproduct arrow. -/
def callerArrowInjection {X Y : J → EnrichedFunctorCat PointedCGWH.{u, v} I} (c : Cofan X) (d : Cofan Y)
    (f : ∀ j, X j ⟶ Y j) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.inj j ≫ p = f j ≫ d.inj j) (j : J) :
    Arrow.mk (f j) ⟶ Arrow.mk p :=
  Arrow.homMk (c.inj j) (d.inj j) (hp j)

/-- The actual original caller cylinder receives every complete original cylinder. -/
def callerCylinderCofan {X Y : J → EnrichedFunctorCat PointedCGWH.{u, v} I} (c : Cofan X) (d : Cofan Y)
    (f : ∀ j, X j ⟶ Y j) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.inj j ≫ p = f j ≫ d.inj j) :
    Cofan (fun j => object (Arrow.mk (f j))) :=
  Cofan.mk (object (Arrow.mk p)) (fun j => map (callerArrowInjection c d f p hp j))

/-- The same caller cylinder cofan is colimiting by the original interval,
source-cofan, target-cofan and pushout universal properties. -/
def callerCylinderCofanIsColimit {X Y : J → EnrichedFunctorCat PointedCGWH.{u, v} I}
    (c : Cofan X) (hc : IsColimit c) (d : Cofan Y) (hd : IsColimit d)
    (f : ∀ j, X j ⟶ Y j) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.inj j ≫ p = f j ≫ d.inj j) :
    IsColimit (callerCylinderCofan c d f p hp) := by
  let T := PointedCGWH.EnrichedIntervalCylinder.functor (I := I)
  let _ : PreservesColimitsOfSize.{w, w} T :=
    (ScalarLeibniz.adjunction PointedCGWH.IntervalCoefficient.interval.{u, v}).leftAdjoint_preservesColimits
  have hcMk : IsColimit (Cofan.mk c.pt c.inj) :=
    IsColimit.ofIsoColimit hc (Cocone.ext (Iso.refl _) (by rintro ⟨j⟩; simp [Cofan.inj]))
  let tc : Cofan (fun j => PointedCGWH.EnrichedIntervalCylinder.object (X j)) :=
    Cofan.mk (PointedCGWH.EnrichedIntervalCylinder.object c.pt)
      (fun j => tensorLeftMap PointedCGWH.IntervalCoefficient.interval (c.inj j))
  let htc : IsColimit tc := isColimitCofanMkObjOfIsColimit T X c.inj hcMk
  let intervalDesc (s : Cofan (fun j => object (Arrow.mk (f j)))) :
      PointedCGWH.EnrichedIntervalCylinder.object c.pt ⟶ s.pt :=
    Cofan.IsColimit.desc htc (fun j => intervalLeg (Arrow.mk (f j)) ≫ s.inj j)
  let targetDesc (s : Cofan (fun j => object (Arrow.mk (f j)))) : d.pt ⟶ s.pt :=
    Cofan.IsColimit.desc hd (fun j => targetLeg (Arrow.mk (f j)) ≫ s.inj j)
  have hInterval (s : Cofan (fun j => object (Arrow.mk (f j)))) (j : J) :
      tensorLeftMap PointedCGWH.IntervalCoefficient.interval (c.inj j) ≫ intervalDesc s =
        intervalLeg (Arrow.mk (f j)) ≫ s.inj j :=
    Cofan.IsColimit.fac htc _ j
  have hTarget (s : Cofan (fun j => object (Arrow.mk (f j)))) (j : J) :
      d.inj j ≫ targetDesc s = targetLeg (Arrow.mk (f j)) ≫ s.inj j :=
    Cofan.IsColimit.fac hd _ j
  have hCondition (s : Cofan (fun j => object (Arrow.mk (f j)))) :
      PointedCGWH.EnrichedIntervalCylinder.inclusion 0 c.pt ≫ intervalDesc s =
        p ≫ targetDesc s := by
    apply Cofan.IsColimit.hom_ext hc
    intro j
    calc
      c.inj j ≫ (PointedCGWH.EnrichedIntervalCylinder.inclusion 0 c.pt ≫ intervalDesc s) =
          (PointedCGWH.EnrichedIntervalCylinder.inclusion 0 (X j) ≫
            tensorLeftMap PointedCGWH.IntervalCoefficient.interval (c.inj j)) ≫
            intervalDesc s := by
              rw [← Category.assoc, PointedCGWH.EnrichedIntervalCylinder.inclusion_naturality]
      _ = PointedCGWH.EnrichedIntervalCylinder.inclusion 0 (X j) ≫
          (intervalLeg (Arrow.mk (f j)) ≫ s.inj j) := by rw [Category.assoc, hInterval]
      _ = f j ≫ (targetLeg (Arrow.mk (f j)) ≫ s.inj j) := by
        have hAttach : PointedCGWH.EnrichedIntervalCylinder.inclusion 0 (X j) ≫
            intervalLeg (Arrow.mk (f j)) = f j ≫ targetLeg (Arrow.mk (f j)) :=
          PointedCGWH.EnrichedIntervalMappingCylinderDeformation.attachment_condition (Arrow.mk (f j))
        rw [← Category.assoc, hAttach, Category.assoc]
      _ = f j ≫ (d.inj j ≫ targetDesc s) := by rw [hTarget]
      _ = c.inj j ≫ (p ≫ targetDesc s) := by rw [← Category.assoc, ← hp, Category.assoc]
  let desc (s : Cofan (fun j => object (Arrow.mk (f j)))) : object (Arrow.mk p) ⟶ s.pt :=
    pushout.desc (intervalDesc s) (targetDesc s) (hCondition s)
  have hDescInterval (s : Cofan (fun j => object (Arrow.mk (f j)))) :
      intervalLeg (Arrow.mk p) ≫ desc s = intervalDesc s := pushout.inl_desc _ _ _
  have hDescTarget (s : Cofan (fun j => object (Arrow.mk (f j)))) :
      targetLeg (Arrow.mk p) ≫ desc s = targetDesc s := pushout.inr_desc _ _ _
  refine Cofan.IsColimit.mk _ desc ?_ ?_
  · intro s j
    change map (callerArrowInjection c d f p hp j) ≫ desc s = s.inj j
    apply pushout.hom_ext
    · rw [← Category.assoc, intervalLeg_map, Category.assoc, hDescInterval]
      exact hInterval s j
    · rw [← Category.assoc, targetLeg_map, Category.assoc, hDescTarget]
      exact hTarget s j
  · intro s m hm
    change object (Arrow.mk p) ⟶ s.pt at m
    change ∀ j, map (callerArrowInjection c d f p hp j) ≫ m = s.inj j at hm
    apply pushout.hom_ext
    · rw [hDescInterval]
      apply Cofan.IsColimit.hom_ext htc
      intro j
      change tensorLeftMap PointedCGWH.IntervalCoefficient.interval (c.inj j) ≫ (intervalLeg (Arrow.mk p) ≫ m) =
        tensorLeftMap PointedCGWH.IntervalCoefficient.interval (c.inj j) ≫ intervalDesc s
      have hLeg : intervalLeg (Arrow.mk (f j)) ≫ map (callerArrowInjection c d f p hp j) =
          tensorLeftMap PointedCGWH.IntervalCoefficient.interval (c.inj j) ≫
            intervalLeg (Arrow.mk p) := intervalLeg_map (callerArrowInjection c d f p hp j)
      rw [hInterval, ← Category.assoc, ← hLeg, Category.assoc]
      exact congrArg (fun k => intervalLeg (Arrow.mk (f j)) ≫ k) (hm j)
    · rw [hDescTarget]
      apply Cofan.IsColimit.hom_ext hd
      intro j
      have hLeg : targetLeg (Arrow.mk (f j)) ≫ map (callerArrowInjection c d f p hp j) =
          d.inj j ≫ targetLeg (Arrow.mk p) := targetLeg_map (callerArrowInjection c d f p hp j)
      rw [hTarget, ← Category.assoc, ← hLeg, Category.assoc]
      exact congrArg (fun k => targetLeg (Arrow.mk (f j)) ≫ k) (hm j)

variable [HasCoproductsOfShape J (EnrichedFunctorCat PointedCGWH.{u, v} I)]

/-- The complete original coproduct of cylinders is the actual cylinder of
the original coproduct map, with every component Arrow square retained. -/
def sigmaIso {X Y : J → EnrichedFunctorCat PointedCGWH.{u, v} I} (f : ∀ j, X j ⟶ Y j) :
    (∐ fun j => object (Arrow.mk (f j))) ≅ object (Arrow.mk (Limits.Sigma.map f)) :=
  (coproductIsCoproduct _).coconePointUniqueUpToIso
    (callerCylinderCofanIsColimit (Cofan.mk (∐ X) (Sigma.ι X)) (coproductIsCoproduct X)
      (Cofan.mk (∐ Y) (Sigma.ι Y)) (coproductIsCoproduct Y) f (Limits.Sigma.map f)
      (fun j => Sigma.ι_map f j))

omit B in
/-- Every forward comparison leg is the original full mapping-cylinder Arrow map. -/
theorem sigmaIso_hom_injection {X Y : J → EnrichedFunctorCat PointedCGWH.{u, v} I} (f : ∀ j, X j ⟶ Y j) (j : J) :
    Sigma.ι (fun j => object (Arrow.mk (f j))) j ≫ (sigmaIso f).hom =
      map (Arrow.homMk (f := Arrow.mk (f j)) (g := Arrow.mk (Limits.Sigma.map f))
        (Sigma.ι X j) (Sigma.ι Y j) (Sigma.ι_map f j)) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct _)
    (callerCylinderCofanIsColimit _ (coproductIsCoproduct X) _ (coproductIsCoproduct Y)
      f (Limits.Sigma.map f) (fun j => Sigma.ι_map f j)) ⟨j⟩

omit B in
/-- The same comparison identifies the whole original retraction maps. -/
theorem sigmaIso_hom_retraction {X Y : J → EnrichedFunctorCat PointedCGWH.{u, v} I} (f : ∀ j, X j ⟶ Y j) :
    (sigmaIso f).hom ≫ retraction (Arrow.mk (Limits.Sigma.map f)) =
      Limits.Sigma.map (fun j => retraction (Arrow.mk (f j))) := by
  apply Sigma.hom_ext
  intro j
  rw [← Category.assoc, sigmaIso_hom_injection, map_retraction, Sigma.ι_map]
  rfl

omit B in
/-- The inverse comparison retains the opposite complete original retraction equation. -/
theorem sigmaIso_inv_retraction {X Y : J → EnrichedFunctorCat PointedCGWH.{u, v} I} (f : ∀ j, X j ⟶ Y j) :
    (sigmaIso f).inv ≫ Limits.Sigma.map (fun j => retraction (Arrow.mk (f j))) =
      retraction (Arrow.mk (Limits.Sigma.map f)) := by
  rw [← sigmaIso_hom_retraction, Iso.inv_hom_id_assoc]

/-- Coproducts of the same actual cylinder projections are level weak by
their genuine original SDR, for arbitrary source and target endpoints. -/
theorem sigmaRetraction_levelWeak {X Y : J → EnrichedFunctorCat PointedCGWH.{u, v} I} (f : ∀ j, X j ⟶ Y j) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)
      (Limits.Sigma.map (fun j => retraction (Arrow.mk (f j)))) := by
  let _ : WeakEquivalence (retraction (Arrow.mk (Limits.Sigma.map f))) :=
    PointedCGWH.EnrichedIntervalMappingCylinderLevelSDR.retraction_weakEquivalence _
  have h : WeakEquivalence ((sigmaIso f).hom ≫ retraction (Arrow.mk (Limits.Sigma.map f))) :=
    inferInstance
  rw [sigmaIso_hom_retraction] at h
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp h

end PointedCGWH.EnrichedIntervalMappingCylinder.Coproducts
