/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.StrongDeformationData

/-!
# Strong native cylinder deformations transpose endpoint lifting

An original strong deformation retains the strict retraction and the
whole stationary source cylinder. Lifting its actual endpoint-one corner
rectifies an arbitrary original square while preserving its full top and
bottom maps. This is a lifting theorem with independent object and Hom
universes and no model or weak-equivalence outcome hypothesis.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace HomotopicalAlgebra.Precylinder.StrongDeformationData

/-- Lifting the actual endpoint-one corner of a full strong deformation lifts its original map,
preserving
  the whole supplied square. -/
theorem hasLiftingProperty_of_endpointCorner {C : Type u} [Category.{v} C] [HasPushouts C]
    {P : Precylinder (𝟭 C)} {X Y E F : C} {i : X ⟶ Y} (D : P.StrongDeformationData i)
    (p : E ⟶ F) [HasLiftingProperty (P.endpointCorner i 1) p] : HasLiftingProperty i p := by
  refine ⟨fun {a b} sq => ?_⟩
  let r := D.retraction
  let H := D.homotopy
  have overlap : i ≫ (r ≫ a) = (P.app X).endpoint 1 ≫ ((P.app X).π ≫ a) := by
    rw [← Category.assoc, D.retract, Category.id_comp]
    rw [← Category.assoc, Precylinder.endpoint_π, Category.id_comp]
  let top := pushout.desc (r ≫ a) ((P.app X).π ≫ a) overlap
  let bottom := H.h ≫ b
  have q : CommSq top (P.endpointCorner i 1) p bottom := by
    constructor
    apply pushout.hom_ext
    · rw [← Category.assoc (pushout.inl i ((P.app X).endpoint 1)) top p]
      rw [show pushout.inl i ((P.app X).endpoint 1) ≫ top = r ≫ a from pushout.inl_desc ..]
      rw [Precylinder.inl_endpointCorner_assoc]
      change (r ≫ a) ≫ p = (P.app Y).i₁ ≫ (H.h ≫ b)
      rw [← Category.assoc (P.app Y).i₁ H.h b, H.h₁, Category.assoc, sq.w]
      exact (Category.assoc r i b).symm
    · rw [← Category.assoc (pushout.inr i ((P.app X).endpoint 1)) top p]
      rw [show pushout.inr i ((P.app X).endpoint 1) ≫ top = (P.app X).π ≫ a from pushout.inr_desc
        ..]
      rw [Precylinder.inr_endpointCorner_assoc]
      change ((P.app X).π ≫ a) ≫ p = P.I.map i ≫ (H.h ≫ b)
      rw [← Category.assoc (P.I.map i) H.h b, D.stationary, Category.assoc, sq.w]
      exact (Category.assoc (P.app X).π i b).symm
  have restriction : P.I.map i ≫ q.lift = (P.app X).π ≫ a := by
    have h := congrArg (fun z => pushout.inr i ((P.app X).endpoint 1) ≫ z) q.fac_left
    simpa only [Precylinder.inr_endpointCorner_assoc, top, pushout.inr_desc] using h
  refine CommSq.HasLift.mk' ⟨(P.app Y).i₀ ≫ q.lift, ?_, ?_⟩
  · calc
      i ≫ ((P.app Y).i₀ ≫ q.lift) = (P.app X).i₀ ≫ (P.I.map i ≫ q.lift) :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ q.lift) (P.i₀.naturality i)).trans (Category.assoc _ _ _))
      _ = (P.app X).i₀ ≫ ((P.app X).π ≫ a) := congrArg (fun z => (P.app X).i₀ ≫ z) restriction
      _ = a := (Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ a) (P.app X).i₀_π).trans (Category.id_comp _))
  · calc
      ((P.app Y).i₀ ≫ q.lift) ≫ p = (P.app Y).i₀ ≫ bottom :=
        (Category.assoc _ _ _).trans (congrArg (fun z => (P.app Y).i₀ ≫ z) q.fac_right)
      _ = b := (Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ b) H.h₀).trans (Category.id_comp _))

end HomotopicalAlgebra.Precylinder.StrongDeformationData
