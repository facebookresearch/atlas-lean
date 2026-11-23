/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.MappingCylinder.SmallCylinder

noncomputable section

open Topology PreAbstractSimplicialComplex
open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder

universe u v

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.boundedSmallDeformation
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.boundedSmallDeformation

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.boundedSmallDeformation_support_in_controlHalo
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.boundedSmallDeformation_support_in_controlHalo

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.controlHalo
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.controlHalo

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.controlHalo_contains
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.controlHalo_contains

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.copiedCone_face_card_le
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.copiedCone_face_card_le

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.domainIntoSmall
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.domainIntoSmall

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallAssociatedCone
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallAssociatedCone

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallAssociatedCone_face_card_le
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallAssociatedCone_face_card_le

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallConeApex
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallConeApex

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallCopiedDomain
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallCopiedDomain

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallCopiedDomain_closed
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallCopiedDomain_closed

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallCopiedDomain_point
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallCopiedDomain_point

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallCopied_old_disjoint
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallCopied_old_disjoint

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallCylinder
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallCylinder

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallCylinderDeformation
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallCylinderDeformation

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallCylinderDeformation_face_support
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallCylinderDeformation_face_support

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallCylinderDeformation_old
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallCylinderDeformation_old

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallCylinder_le
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallCylinder_le

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallIntoCone
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallIntoCone

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallIntoCone_point
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallIntoCone_point

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallOldTarget
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallOldTarget

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallOldTarget_point
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallOldTarget_point

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallOrdinaryConeAttachment
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallOrdinaryConeAttachment
#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallOrdinaryConeAttachment_point
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallOrdinaryConeAttachment_point

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallOrdinaryConeAttachment_apex
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallOrdinaryConeAttachment_apex

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallOrdinaryConeAttachment_base
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallOrdinaryConeAttachment_base

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallOrdinaryConeAttachment_closed
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallOrdinaryConeAttachment_closed

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallOrdinaryConeAttachment_isPushout
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallOrdinaryConeAttachment_isPushout

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallRetraction
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallRetraction

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallRetraction_copied
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallRetraction_copied

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallRetraction_old
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.smallRetraction_old

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.small_all_face_card_le
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.small_all_face_card_le

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.small_domain_le
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.small_domain_le

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.small_mixed_face_card_le
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.small_mixed_face_card_le

#check PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.small_target_le
#print axioms PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder.small_target_le

/-- No injectivity is assumed: this law preserves the original realization map,
including all folding multiplicities, on every copied source point. -/
example {V : Type u} {W : Type v} (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (f : Morphism P Q)
    (x : (barycentricSubdivision P).Realization) :
    smallRetraction f (smallCopiedDomain f x) = f.realization (barycentricHomeomorph P x) :=
  smallRetraction_copied f x

/-- The dimension estimate separates the bounded source contribution from
arbitrary target faces and does not assume a finite or injective target. -/
example {V : Type u} {W : Type v} (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (f : Morphism P Q) (M N : ℕ)
    (hP : ∀ a : Face P, a.val.card ≤ M) (hQ : ∀ a : Face Q, a.val.card ≤ N)
    (s : Face (smallCylinder f)) : s.val.card ≤ max (M + 1) N :=
  small_all_face_card_le f M N hP hQ s

/-- For the empty source, finiteness is derived and the whole old target stays
fixed at every time in the constructed ordinary deformation. -/
example {V : Type u} {W : Type v} (Q : PreAbstractSimplicialComplex W)
    (f : Morphism (⊥ : PreAbstractSimplicialComplex V) Q) (t : unitInterval)
    (y : Q.Realization) :
    letI : IsEmpty (Face (⊥ : PreAbstractSimplicialComplex V)) := ⟨fun a => a.property⟩
    letI : Finite (Face (⊥ : PreAbstractSimplicialComplex V)) := inferInstance
    smallCylinderDeformation f (t, smallOldTarget f y) = smallOldTarget f y := by
  let : IsEmpty (Face (⊥ : PreAbstractSimplicialComplex V)) := ⟨fun a => a.property⟩
  let : Finite (Face (⊥ : PreAbstractSimplicialComplex V)) := inferInstance
  exact smallCylinderDeformation_old f t y

-- Every ordinary cone point, including the whole cone interior, has the original coordinates.
example {V : Type u} {W : Type v} {P : PreAbstractSimplicialComplex V}
    {Q : PreAbstractSimplicialComplex W} (f : Morphism P Q) [Finite (Face P)]
    (x : TopCat.cone (TopCat.of (MappingCylinder.domainComplex P W).Realization)) :
    letI : Finite (Face (MappingCylinder.domainComplex P W)) :=
      MappingCylinder.finiteFaces_domainComplex P W
    (MappingCylinder.SmallCylinder.smallOrdinaryConeAttachment f x).point =
      (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex P W) x).point := by
  exact MappingCylinder.SmallCylinder.smallOrdinaryConeAttachment_point f x

end
