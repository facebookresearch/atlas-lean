/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalInjectiveLabelPushforwardWeakMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.StrictIsoHom
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomEqualityTransport

/-!
# The SAME original injective label unit is an isomorphism on every full Hom

The genuine original full family isomorphism carries the original unit
to the unchanged full family inclusion. Its original Hom map is an
identity. Both actual inverse enriched maps and only the true endpoint
equations prove the original full unit Hom map invertible.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.CarrierLabelExtension

/-- The SAME actual original unit has an invertible full Hom map at every original source pair. -/
theorem inclusion_hom_isIso {O : Type u} (C : Carrier.{u}) (a : C → O) (ha : Function.Injective a)
    (x y : C) : IsIso ((inclusion C a).map x y) := by
  let E := InjectiveLabelFamilies.fullIso a ha (CarrierReindexing.source C)
  let i := DisjointCoproduct.inl C (InjectiveLabelFamilies.isolated a).val
  have fac : inclusion C a ≫ E.hom = i :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun F => F ≫ (InjectiveLabelFamilies.familyIso a ha (CarrierReindexing.source C)).hom)
        (InjectiveLabelFamilies.toObject_unit a ha (CarrierReindexing.source C))).trans
          (InjectiveLabelFamilies.inclusion_familyIso a ha (CarrierReindexing.source C)))
  have h := EnrichedFunctor.homMap_transport_of_eq fac x y
  let t := congrArg₂ (fun b c : InjectiveLabelFamilies.family a (CarrierReindexing.source C) => b ⟶[SSet.{u}] c)
    (congrArg (fun F => F.obj x) fac) (congrArg (fun F => F.obj y) fac)
  let T : (((inclusion C a ≫ E.hom).obj x) ⟶[SSet.{u}] ((inclusion C a ≫ E.hom).obj y)) ≅
      (i.obj x ⟶[SSet.{u}] i.obj y) := eqToIso t
  have hi : IsIso (((inclusion C a).map x y ≫ E.hom.map ((inclusion C a).obj x) ((inclusion C a).obj y)) ≫ T.hom) :=
    (congrArg (fun f : (x ⟶[SSet.{u}] y) ⟶ (i.obj x ⟶[SSet.{u}] i.obj y) => IsIso f) h).mpr
      (show IsIso (i.map x y) from by change IsIso (𝟙 (x ⟶[SSet.{u}] y)); infer_instance)
  have hm : IsIso ((inclusion C a).map x y ≫ E.hom.map ((inclusion C a).obj x) ((inclusion C a).obj y)) :=
    @IsIso.of_isIso_comp_right SSet.{u} inferInstance
      (x ⟶[SSet.{u}] y) (((inclusion C a ≫ E.hom).obj x) ⟶[SSet.{u}] ((inclusion C a ≫ E.hom).obj y))
      (i.obj x ⟶[SSet.{u}] i.obj y)
      ((inclusion C a).map x y ≫ E.hom.map ((inclusion C a).obj x) ((inclusion C a).obj y)) T.hom T.isIso_hom hi
  exact @IsIso.of_isIso_comp_right SSet.{u} inferInstance
    (((inclusion C a ≫ E.hom).obj x) ⟶[SSet.{u}] ((inclusion C a ≫ E.hom).obj y))
    ((inclusion C a).obj x ⟶[SSet.{u}] (inclusion C a).obj y) (x ⟶[SSet.{u}] y)
    ((inclusion C a).map x y) (E.hom.map ((inclusion C a).obj x) ((inclusion C a).obj y))
    (isoHomIso E _ _).isIso_hom hm

end CategoryTheory.SimplicialEnrichment.CarrierLabelExtension
