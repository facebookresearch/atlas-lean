/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalInjectiveLabelFamilies
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabelCarrierUnit
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectVertexMaps

/-!
# The SAME actual injective label-pushforward is the original family plus isolated labels

Both genuine whole enriched comparisons retain every original source
generator and every unused object. The actual presentation universal
property and the genuine full carrier coproduct prove both inverses.
No Hom or model comparison outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.InjectiveLabelFamilies
open FixedObjects

variable {A O : Type u} (a : A → O) (ha : Function.Injective a) (C : FixedObjects A)

/-- The SAME original injected source as an actual restricted fixed-label map. -/
def unitInput : C ⟶ LabelRestriction.object a (object a ha C) :=
  CarrierLabelReadback.map C (fun s => vertex (object a ha C) (a s))
    (inclusion a ha C) (inclusion_vertex a ha C)

/-- The actual label-presentation descender into the SAME original family. -/
def toObject : LabelPushforward.object a C ⟶ object a ha C :=
  LabelPushforward.desc a C (unitInput a ha C)

/-- The SAME complete original source unit maps to the actual original family inclusion. -/
theorem toObject_unit : LabelPushforward.carrierUnit a C ≫ (toObject a ha C).val =
    inclusion a ha C :=
  (LabelPushforward.carrierUnit_desc a C (unitInput a ha C)).trans
    (CarrierLabelReadback.map_fac C (fun s => vertex (object a ha C) (a s))
      (inclusion a ha C) (inclusion_vertex a ha C))

/-- The whole original disjoint family evaluates by the SAME source unit and every unused vertex. -/
def fromFamily : family a C ⟶ (LabelPushforward.object a C).val :=
  DisjointCoproduct.desc (LabelPushforward.carrierUnit a C)
    (BergnerFixedInitialObjects.desc (complement a)
      (fun o => vertex (LabelPushforward.object a C) o.val))

/-- Every original full family object is read back at its SAME actual target label. -/
theorem fromFamily_vertex (p : family a C) :
    (fromFamily a C).obj p = vertex (LabelPushforward.object a C) (familyEquiv a ha C p) := by
  cases p with
  | inl c =>
      change (LabelPushforward.carrierUnit a C).obj c =
        vertex (LabelPushforward.object a C) (a (label C c))
      exact (congrArg (LabelPushforward.carrierUnit a C).obj (vertex_label C c).symm).trans
        (LabelPushforward.carrierUnit_vertex a C (label C c))
  | inr c =>
      change (BergnerFixedInitialObjects.desc (complement a)
        (fun o => vertex (LabelPushforward.object a C) o.val)).obj c =
          vertex (LabelPushforward.object a C) (label (isolated a) c).val
      exact (congrArg (BergnerFixedInitialObjects.desc (complement a)
        (fun o => vertex (LabelPushforward.object a C) o.val)).obj
          (vertex_label (isolated a) c).symm).trans
        (BergnerFixedInitialObjects.desc_vertex (complement a)
          (fun o => vertex (LabelPushforward.object a C) o.val) (label (isolated a) c))

/-- The SAME whole carrier map back to the original label-pushforward presentation. -/
def fromObjectCarrier : (object a ha C).val ⟶ (LabelPushforward.object a C).val :=
  (familyIso a ha C).hom ≫ fromFamily a C

/-- Every individually supplied target label is retained by the actual whole inverse. -/
theorem fromObject_vertex (o : O) :
    (fromObjectCarrier a ha C).obj (vertex (object a ha C) o) =
      vertex (LabelPushforward.object a C) o := by
  exact (fromFamily_vertex a ha C ((familyEquiv a ha C).symm o)).trans
    (congrArg (vertex (LabelPushforward.object a C)) ((familyEquiv a ha C).apply_symm_apply o))

/-- The SAME full inverse carrier map with its genuine original fixed-label equations. -/
def fromObject : object a ha C ⟶ LabelPushforward.object a C :=
  ofVertexEquation (fromObjectCarrier a ha C) (fromObject_vertex a ha C)

/-- The actual original source inclusion reads back the SAME complete original source unit. -/
theorem inclusion_fromObject : inclusion a ha C ≫ (fromObject a ha C).val =
    LabelPushforward.carrierUnit a C := by
  change inclusion a ha C ≫ ((familyIso a ha C).hom ≫ fromFamily a C) = _
  rw [← Category.assoc, inclusion_familyIso]
  exact DisjointCoproduct.inl_desc _ _

/-- Both full original maps compose to the SAME entire label-presentation identity. -/
theorem toObject_fromObject : toObject a ha C ≫ fromObject a ha C = 𝟙 (LabelPushforward.object a C) := by
  apply LabelPushforward.carrierUnit_ext a C
  change LabelPushforward.carrierUnit a C ≫ ((toObject a ha C).val ≫ (fromObject a ha C).val) =
    LabelPushforward.carrierUnit a C ≫ 𝟙 (LabelPushforward.object a C).val
  rw [← Category.assoc, toObject_unit, inclusion_fromObject, Category.comp_id]

/-- Every original family map is read back by the SAME full inverse comparison. -/
theorem fromFamily_toObject : fromFamily a C ≫ (toObject a ha C).val = (familyIso a ha C).inv := by
  let i := DisjointCoproduct.inl C.val (isolated a).val
  let j := DisjointCoproduct.inr C.val (isolated a).val
  have hi : i ≫ (fromFamily a C ≫ (toObject a ha C).val) = i ≫ (familyIso a ha C).inv := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k : C.val ⟶ (LabelPushforward.object a C).val =>
        k ≫ (toObject a ha C).val)
          (DisjointCoproduct.inl_desc (LabelPushforward.carrierUnit a C)
            (BergnerFixedInitialObjects.desc (complement a)
              (fun o => vertex (LabelPushforward.object a C) o.val)))).trans (toObject_unit a ha C))
  have hj : j ≫ (fromFamily a C ≫ (toObject a ha C).val) = j ≫ (familyIso a ha C).inv := by
    apply (BergnerFixedInitialObjects.homEquiv (complement a) (object a ha C).val).injective
    funext o
    change (toObject a ha C).val.obj ((fromFamily a C).obj (Sum.inr (vertex (isolated a) o))) =
      familyEquiv a ha C (Sum.inr (vertex (isolated a) o))
    have h := fromFamily_vertex a ha C (Sum.inr (vertex (isolated a) o))
    rw [familyEquiv_inr] at h
    rw [h]
    exact (map_vertex (toObject a ha C) o.val).trans (familyEquiv_inr a ha C o).symm
  exact (DisjointCoproduct.desc_unique (i ≫ (familyIso a ha C).inv)
    (j ≫ (familyIso a ha C).inv) (fromFamily a C ≫ (toObject a ha C).val) hi hj).trans
      (DisjointCoproduct.desc_unique (i ≫ (familyIso a ha C).inv)
        (j ≫ (familyIso a ha C).inv) (familyIso a ha C).inv rfl rfl).symm

/-- Both full original maps compose to the SAME entire original separated-family identity. -/
theorem fromObject_toObject : fromObject a ha C ≫ toObject a ha C = 𝟙 (object a ha C) := by
  apply Functor.Fiber.hom_ext
  change ((familyIso a ha C).hom ≫ fromFamily a C) ≫ (toObject a ha C).val = 𝟙 (object a ha C).val
  rw [Category.assoc, fromFamily_toObject]
  exact (familyIso a ha C).hom_inv_id

/-- The SAME actual original injective-label pushforward is genuinely isomorphic to the full original family. -/
def pushforwardIso : LabelPushforward.object a C ≅ object a ha C where
  hom := toObject a ha C
  inv := fromObject a ha C
  hom_inv_id := toObject_fromObject a ha C
  inv_hom_id := fromObject_toObject a ha C

end CategoryTheory.SimplicialEnrichment.InjectiveLabelFamilies
