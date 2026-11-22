/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnitGroupoidCloneUnitMap
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnitGroupoidFunctorReadback
import MathlibExt.AlgebraicTopology.SimplicialCategory.SimplicialFunctorObjectTransport

/-!
# The actual full original unit-groupoid clone descender

The original functor F and the supplied actual unit-category isomorphism
from F(x) to y determine a complete original clone functor. Its old
objects retain F and its new label retains y. Both original full family
triangles are proved on the SAME coefficient maps. The canonical Hom
isomorphism transports full original Homs, not only unit vertices.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.UnitGroupoidClone
variable (C : Carrier.{u}) (x : C) {E : Type v} [EnrichedCategory SSet.{u} E]
  (F : EnrichedFunctor SSet.{u} C E) (y : E)
  (α : ForgetEnrichment.of SSet.{u} (F.obj x) ≅ ForgetEnrichment.of SSet.{u} y)

/-- The SAME full original functor through the actual canonical clone projection. -/
def descBase : EnrichedFunctor SSet.{u} (object C x) E := (projection C x).comp SSet.{u} F

/-- The original old image objects and the SAME supplied actual new object. -/
def descObjects : C ⊕ PUnit.{u+1} → E := Sum.elim F.obj (fun _ => y)

/-- Original objects retain identity isomorphisms, and the actual new label retains the SAME supplied original unit
isomorphism. -/
def descIsos : ∀ a : object C x,
    ForgetEnrichment.of SSet.{u} ((descBase C x F).obj a) ≅
      ForgetEnrichment.of SSet.{u} (descObjects C F y a)
  | .inl _a => Iso.refl _
  | .inr _a => α

/-- The genuine entire original clone functor, retaining every actual original full Hom map. -/
def cloneDesc : EnrichedFunctor SSet.{u} (object C x) E :=
  SSet.transportObjects (descBase C x F) (descObjects C F y) (descIsos C x F y α)

/-- Every original old object keeps its SAME supplied F image. -/
theorem cloneDesc_old (a : C) : (cloneDesc C x F y α).obj (Sum.inl a) = F.obj a := rfl

/-- The original new clone label keeps the SAME actual supplied target object. -/
theorem cloneDesc_new : (cloneDesc C x F y α).obj (newObject C x) = y := rfl

/-- The SAME whole original source inclusion factors through the actual clone descender to F. -/
theorem cloneDesc_left : (inclusion C x).comp SSet.{u} (cloneDesc C x F y α) = F := by
  apply EnrichedFunctor.ext SSet.{u} (C := C) (D := E)
    (F := (inclusion C x).comp SSet.{u} (cloneDesc C x F y α)) (G := F) (fun _a => rfl)
  intro a b
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro p
  have ht := congrArg (fun e : (F.obj a ⟶[SSet.{u}] F.obj b) ≅ (F.obj a ⟶[SSet.{u}] F.obj b) =>
    e.hom.app q ((F.map a b).app q p))
    (Iso.eHomCongr_refl SSet.{u} (ForgetEnrichment.of SSet.{u} (F.obj a))
      (ForgetEnrichment.of SSet.{u} (F.obj b)))
  exact ht

/-- The SAME whole forward unit-groupoid coefficient of the actual descender is the supplied original scalar
isomorphism. -/
theorem cloneDesc_forward (q : SimplexCategoryᵒᵖ) :
    (((unitMap C x).comp SSet.{u} (cloneDesc C x F y α)).map
      OriginalTwoLabelUnitGroupoid.source OriginalTwoLabelUnitGroupoid.target).app q PUnit.unit =
      (SSet.unitScalarFunctor E q).map α.hom := by
  let U := SSet.unitScalarFunctor E q
  let A := U.obj (ForgetEnrichment.of SSet.{u} (F.obj x))
  let H : A ⟶ A := (F.map x x).app q ((eId SSet.{u} x).app q PUnit.unit)
  have hF : H = 𝟙 A := congrArg (fun h : 𝟙_ SSet.{u} ⟶ (F.obj x ⟶[SSet.{u}] F.obj x) =>
    h.app q PUnit.unit) (F.map_id x)
  have he := SSet.transportObjects_scalar (descBase C x F) (descObjects C F y)
    (descIsos C x F y α) q (Sum.inl x) (newObject C x) ((eId SSet.{u} x).app q PUnit.unit)
  have hi : U.map (𝟙 (ForgetEnrichment.of SSet.{u} (F.obj x))) = 𝟙 A := U.map_id _
  have hc : U.map (𝟙 (ForgetEnrichment.of SSet.{u} (F.obj x))) ≫ H ≫ U.map α.hom = U.map α.hom :=
    (congrArg₂ (fun (a b : A ⟶ A) => a ≫ b ≫ U.map α.hom) hi hF).trans
      ((congrArg (fun h => (𝟙 A) ≫ h) (Category.id_comp (U.map α.hom))).trans (Category.id_comp _))
  exact he.trans hc

/-- The SAME actual original full unit-groupoid functor factors through the descender with every original coefficient
retained. -/
theorem cloneDesc_unit : (unitMap C x).comp SSet.{u} (cloneDesc C x F y α) =
    OriginalTwoLabelUnitGroupoid.ofIso (F.obj x) y α := by
  let G := (unitMap C x).comp SSet.{u} (cloneDesc C x F y α)
  have he : OriginalTwoLabelUnitGroupoid.originalIso G = α := by
    apply Iso.ext
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro p
    cases p
    exact (OriginalTwoLabelUnitGroupoid.originalIso_hom_scalar G q).trans (cloneDesc_forward C x F y α q)
  have hr := OriginalTwoLabelUnitGroupoid.ofIso_readback G
  rw [he] at hr
  exact hr.symm

end CategoryTheory.SimplicialEnrichment.UnitGroupoidClone
