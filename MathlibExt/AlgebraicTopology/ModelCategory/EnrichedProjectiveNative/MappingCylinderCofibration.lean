/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinderModel
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.IntervalGood

/-!
# Cofibrancy of the literal original native mapping-cylinder source

The original native mapping-cylinder pushout is also the pushout of its
genuine joint interval inclusion along the two original caller maps. The
whole coproduct-to-cylinder map is therefore a cofibration. For genuinely
cofibrant native source and target, its original second-endpoint source
factor is a cofibration. No pushout or cofibrancy dictionary is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.EnrichedIntervalMappingCylinderModel

open PointedCGWH.EnrichedIntervalMappingCylinder
open PointedCGWH.EnrichedIntervalCylinder
open PointedCGWH.EnrichedIntervalCylinderModel

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  MonoidalClosed.enrichedCategorySelf

/-- The first joint slot retains f into its target; the second retains the original source. -/
abbrev attachmentMap (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    f.left ⨿ f.left ⟶ f.left ⨿ f.right :=
  coprod.desc (f.hom ≫ coprod.inr) coprod.inl

/-- The actual coproduct descent of both original mapping-cylinder factors. -/
abbrev foldMap (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    f.left ⨿ f.right ⟶ EnrichedIntervalMappingCylinder.object f :=
  coprod.desc (source f) (targetLeg f)

omit B in
private theorem attachment_condition (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    jointMap f.left ≫ intervalLeg f = attachmentMap f ≫ foldMap f := by
  change coprod.desc (inclusion 0 f.left) (inclusion 1 f.left) ≫ intervalLeg f =
    attachmentMap f ≫ foldMap f
  apply coprod.hom_ext
  · simp only [attachmentMap, foldMap, Category.assoc,
      coprod.inl_desc_assoc, coprod.inr_desc]
    exact pushout.condition
  · simp only [attachmentMap, foldMap,
      coprod.inr_desc_assoc, coprod.inl_desc]
    rfl

omit B in
private theorem desc_condition (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (s : PushoutCocone (jointMap f.left) (attachmentMap f)) :
    inclusion 0 f.left ≫ s.inl = f.hom ≫ (coprod.inr ≫ s.inr) := by
  have h := congrArg (fun t => (coprod.inl : f.left ⟶ f.left ⨿ f.left) ≫ t) s.condition
  change (coprod.inl : f.left ⟶ f.left ⨿ f.left) ≫
      coprod.desc (inclusion 0 f.left) (inclusion 1 f.left) ≫ s.inl =
    coprod.inl ≫ attachmentMap f ≫ s.inr at h
  simpa only [attachmentMap, Category.assoc, coprod.inl_desc_assoc] using h

omit B in
private theorem desc_condition_second (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (s : PushoutCocone (jointMap f.left) (attachmentMap f)) :
    inclusion 1 f.left ≫ s.inl = (coprod.inl : f.left ⟶ f.left ⨿ f.right) ≫ s.inr := by
  have h := congrArg (fun t => (coprod.inr : f.left ⟶ f.left ⨿ f.left) ≫ t) s.condition
  change (coprod.inr : f.left ⟶ f.left ⨿ f.left) ≫
      coprod.desc (inclusion 0 f.left) (inclusion 1 f.left) ≫ s.inl =
    coprod.inr ≫ attachmentMap f ≫ s.inr at h
  simpa only [attachmentMap, Category.assoc, coprod.inr_desc_assoc] using h

omit B in
/-- The whole original mapping-cylinder pushout is the actual joint-boundary attachment square. -/
theorem attachment_isPushout (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    IsPushout (jointMap f.left) (attachmentMap f) (intervalLeg f) (foldMap f) := by
  let hc : IsColimit (PushoutCocone.mk (intervalLeg f) (foldMap f)
      (attachment_condition f)) :=
    PushoutCocone.IsColimit.mk (attachment_condition f)
      (fun s => pushout.desc s.inl (coprod.inr ≫ s.inr) (desc_condition f s))
      (fun s => pushout.inl_desc _ _ _)
      (fun s => by
        apply coprod.hom_ext
        · rw [coprod.inl_desc_assoc, source, Category.assoc, pushout.inl_desc]
          exact desc_condition_second f s
        · rw [coprod.inr_desc_assoc, pushout.inr_desc])
      (fun s m hLeft hRight => by
        apply pushout.hom_ext
        · rw [pushout.inl_desc]
          exact hLeft
        · rw [pushout.inr_desc]
          have h := congrArg (fun t => (coprod.inr : f.right ⟶ f.left ⨿ f.right) ≫ t) hRight
          simpa only [foldMap, Category.assoc, coprod.inr_desc_assoc] using h)
  exact IsPushout.of_isColimit hc

/-- The actual entire coproduct-to-mapping-cylinder map is cofibrant for a cofibrant source. -/
theorem foldMap_cofibration
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) [IsCofibrant f.left] :
    Cofibration (foldMap f) := by
  have hJoint : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) (jointMap f.left) :=
    (HomotopicalAlgebra.cofibration_iff _).mp (jointMap_cofibration f.left)
  exact (HomotopicalAlgebra.cofibration_iff _).mpr
    (MorphismProperty.of_isPushout (attachment_isPushout f).flip hJoint)

/-- The original second-endpoint source factor is an actual native projective cofibration. -/
theorem source_cofibration
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I))
    [IsCofibrant f.left] [IsCofibrant f.right] : Cofibration (source f) := by
  let _ : Cofibration (foldMap f) := foldMap_cofibration f
  have h : Cofibration ((coprod.inl : f.left ⟶ f.left ⨿ f.right) ≫ foldMap f) :=
    inferInstance
  rwa [coprod.inl_desc] at h

end PointedCGWH.EnrichedIntervalMappingCylinderModel
