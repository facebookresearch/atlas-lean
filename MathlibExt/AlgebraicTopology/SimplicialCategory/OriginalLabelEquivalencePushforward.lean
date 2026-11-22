/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabelCarrierUnit
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalLabelPushforwardGlobalPushout
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierReindexingEquivalence
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectVertexMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabelPushforwardQuillen

/-!
# The SAME original label-equivalence pushforward is the actual inverse restriction

The true inverse label equations and the genuine original generator
universal property give both complete enriched inverse maps. The SAME
existing Quillen pushforward therefore proves cofibrancy of restriction
along an actual label equivalence, without a cofibrancy certificate for
the desired restricted object.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.LabelEquivalence
attribute [local instance] FixedObjectModel.modelCategory

variable {A O : Type u} (e : A ≃ O) (C : FixedObjects A)

/-- The SAME full original inverse-label restriction. -/
abbrev restricted : FixedObjects O := LabelRestriction.object e.symm C

/-- The actual original object-equivalence projection with both entire inverse functors. -/
def projectionIso : (restricted e C).val ≅ C.val :=
  CarrierReindexing.equivalenceIso C.val (e.symm.trans (verticesEquiv C))

/-- The actual original source vertex equation uses only the true inverse label identity. -/
theorem source_vertex (s : A) :
    (𝟙 C.val : C.val ⟶ C.val).obj (vertex C s) = vertex C (e.symm (e s)) :=
  (congrArg (vertex C) (e.symm_apply_apply s)).symm

/-- The SAME whole original identity functor as the genuine restricted fixed-label input. -/
def input : C ⟶ LabelRestriction.object e (restricted e C) :=
  CarrierLabelReadback.map C (fun s => vertex C (e.symm (e s))) (𝟙 C.val) (source_vertex e C)

/-- Extend that SAME original full source through its existing label-pushforward presentation. -/
def toRestricted : LabelPushforward.object e C ⟶ restricted e C :=
  LabelPushforward.desc e C (input e C)

/-- The SAME original whole unit and full projection recover the entire original identity. -/
theorem unit_toRestricted_projection :
    LabelPushforward.carrierUnit e C ≫ ((toRestricted e C).val ≫ (projectionIso e C).hom) = 𝟙 C.val := by
  have h := congrArg (fun F : C ⟶ LabelRestriction.object e (restricted e C) =>
    F.val ≫ CarrierReindexing.toTarget C.val (fun s => vertex C (e.symm (e s))))
      (LabelPushforward.unit_desc e C (input e C))
  exact (LabelPushforward.GlobalPushout.target_projection e C (fun o => vertex C (e.symm o))
    (toRestricted e C)).symm.trans
      (h.trans (CarrierLabelReadback.map_fac C (fun s => vertex C (e.symm (e s)))
        (𝟙 C.val) (source_vertex e C)))

/-- The SAME whole original inverse is the actual projection followed by the original carrier unit. -/
def fromRestrictedCarrier : (restricted e C).val ⟶ (LabelPushforward.object e C).val :=
  (projectionIso e C).hom ≫ LabelPushforward.carrierUnit e C

/-- The actual full inverse retains each SAME individual original target label. -/
theorem fromRestricted_vertex (o : O) :
    (fromRestrictedCarrier e C).obj (vertex (restricted e C) o) =
      vertex (LabelPushforward.object e C) o :=
  (LabelPushforward.carrierUnit_vertex e C (e.symm o)).trans
    (congrArg (vertex (LabelPushforward.object e C)) (e.apply_symm_apply o))

/-- The SAME whole original inverse with its genuine fixed-label equations. -/
def fromRestricted : restricted e C ⟶ LabelPushforward.object e C :=
  ofVertexEquation (fromRestrictedCarrier e C) (fromRestricted_vertex e C)

/-- Both entire actual original maps compose to the SAME pushforward identity. -/
theorem toRestricted_fromRestricted : toRestricted e C ≫ fromRestricted e C = 𝟙 (LabelPushforward.object e C) := by
  apply LabelPushforward.carrierUnit_ext e C
  change LabelPushforward.carrierUnit e C ≫
      ((toRestricted e C).val ≫ ((projectionIso e C).hom ≫ LabelPushforward.carrierUnit e C)) =
    LabelPushforward.carrierUnit e C ≫ 𝟙 (LabelPushforward.object e C).val
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ LabelPushforward.carrierUnit e C) (unit_toRestricted_projection e C)).trans
      ((Category.id_comp _).trans (Category.comp_id _).symm))

/-- Both entire actual original maps compose to the SAME inverse-restriction identity. -/
theorem fromRestricted_toRestricted : fromRestricted e C ≫ toRestricted e C = 𝟙 (restricted e C) := by
  apply Functor.Fiber.hom_ext
  apply (cancel_mono (projectionIso e C).hom).mp
  change (((projectionIso e C).hom ≫ LabelPushforward.carrierUnit e C) ≫ (toRestricted e C).val) ≫
    (projectionIso e C).hom = 𝟙 (restricted e C).val ≫ (projectionIso e C).hom
  rw [Category.assoc, Category.assoc, unit_toRestricted_projection, Category.comp_id, Category.id_comp]

/-- The SAME original equivalence pushforward is genuinely the whole original inverse-label restriction. -/
def pushforwardIso : LabelPushforward.object e C ≅ restricted e C where
  hom := toRestricted e C
  inv := fromRestricted e C
  hom_inv_id := toRestricted_fromRestricted e C
  inv_hom_id := fromRestricted_toRestricted e C

/-- Restriction along the SAME actual inverse equivalence preserves genuine source cofibrancy. -/
theorem restricted_isCofibrant [IsCofibrant C] : IsCofibrant (restricted e C) := by
  let _ : IsCofibrant (LabelPushforward.object e C) := LabelPushforward.object_isCofibrant e C
  exact isCofibrant_of_cofibration (pushforwardIso e C).hom

end CategoryTheory.SimplicialEnrichment.FixedObjects.LabelEquivalence
