/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnitGroupoidCloneDesc
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnitGroupoidCloneCoordinates
import MathlibExt.AlgebraicTopology.SimplicialCategory.SimplicialHomCongrFunctorNaturality

/-!
# The SAME original whole clone functor is reconstructed from its actual coordinates

Every original full clone coefficient has its actual original identity
coordinate. Full canonical Hom-congruence naturality therefore recovers
every original functor map from its original old-family restriction and
the actual image of its unit-groupoid coordinate. No reconstruction or
pushout-outcome certificate is supplied as an input.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.UnitGroupoidClone
variable (C : Carrier.{u}) (x : C) {E : Type v} [EnrichedCategory SSet.{u} E]
  (H : EnrichedFunctor SSet.{u} (object C x) E)

/-- The actual descender coordinate family retains the SAME original full functor images of every source coordinate. -/
theorem cloneDescIso_images (a : object C x) :
    HEq (descIsos C x ((inclusion C x).comp SSet.{u} H) (H.obj (newObject C x))
      (H.forget.mapIso (unitCoordinateIso C x)) a)
      (H.forget.mapIso (coordinateIso C x a)) := by
  cases a with
  | inl a =>
    have h : H.forget.mapIso (Iso.refl (ForgetEnrichment.of (C := object C x) SSet.{u} (Sum.inl a))) =
        Iso.refl (ForgetEnrichment.of SSet.{u} (H.obj (Sum.inl a))) := by
      apply Iso.ext
      exact H.forget.map_id _
    exact (heq_of_eq h).symm
  | inr a => cases a; rfl

/-- The SAME complete original functor Hom map is recovered by its actual original folded coordinate. -/
theorem cloneHom_readback (a b : object C x) :
    H.map (Sum.inl (fold C x a)) (Sum.inl (fold C x b)) ≫
        (Iso.eHomCongr SSet.{u} (H.forget.mapIso (coordinateIso C x a))
          (H.forget.mapIso (coordinateIso C x b))).hom = H.map a b :=
  (SSet.homCongr_functor_natural H (coordinateIso C x a) (coordinateIso C x b)).trans
    ((congrArg (fun k : (fold C x a ⟶[SSet.{u}] fold C x b) ⟶
        (fold C x a ⟶[SSet.{u}] fold C x b) => k ≫ H.map a b) (coordinateHom_identity C x a b)).trans
      (Category.id_comp _))

/-- The actual old restriction and SAME original unit-coordinate image reconstruct the entire original clone functor. -/
theorem cloneDesc_readback :
    cloneDesc C x ((inclusion C x).comp SSet.{u} H) (H.obj (newObject C x))
      (H.forget.mapIso (unitCoordinateIso C x)) = H := by
  apply EnrichedFunctor.ext SSet.{u} (C := object C x) (D := E)
    (F := cloneDesc C x ((inclusion C x).comp SSet.{u} H) (H.obj (newObject C x))
      (H.forget.mapIso (unitCoordinateIso C x))) (G := H)
    (fun a => by cases a with | inl a => rfl | inr a => cases a; rfl)
  intro a b
  let A : object C x := a
  let B : object C x := b
  rcases a with a | ⟨⟩ <;> rcases b with b | ⟨⟩
  all_goals
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro p
    have he := cloneHom_readback C x H A B
    have ha := eq_of_heq (cloneDescIso_images C x H A)
    have hb := eq_of_heq (cloneDescIso_images C x H B)
    rw [← ha] at he
    try rw [← hb] at he
    exact congrArg (fun f => f.app q p) he

end CategoryTheory.SimplicialEnrichment.UnitGroupoidClone

namespace CategoryTheory.SimplicialEnrichment.OriginalTwoLabelUnitGroupoid
variable {E : Type v} [EnrichedCategory SSet.{u} E]

/-- The actual original unit-groupoid functor retains the SAME supplied isomorphism on full readback. -/
theorem originalIso_ofIso (a b : E)
    (α : ForgetEnrichment.of SSet.{u} a ≅ ForgetEnrichment.of SSet.{u} b) :
    originalIso (ofIso a b α) = α := by
  apply Iso.ext
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro p
  cases p
  rfl

end CategoryTheory.SimplicialEnrichment.OriginalTwoLabelUnitGroupoid
