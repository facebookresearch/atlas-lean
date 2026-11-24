/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLabelMaps

/-! # The whole changing-object unit and prescribed-label extension

The actual path-presentation unit has its original object function and
original generator maps. Reindexing projections commute with complete
fixed-object functors, retaining every original Hom map and endpoint.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.CarrierLabelExtension
open FixedObjects

private theorem restricted_val_map {A O : Type u} (a : A → O)
    {C D : FixedObjects O} (F : C ⟶ D) (s t : A) :
    (LabelRestriction.map a F).val.map s t = homMap F (a s) (a t) := by
  change 𝟙 (hom C (a s) (a t)) ≫ homMap F (a s) (a t) = homMap F (a s) (a t)
  exact Category.id_comp _

/-- Projection retains the whole original fixed-object functor and its two endpoint maps. -/
theorem restriction_projection {A O : Type u} (a : A → O)
    {C D : FixedObjects O} (F : C ⟶ D) :
    (LabelRestriction.map a F).val ≫
        CarrierReindexing.toTarget D.val (fun s => vertex D (a s)) =
      CarrierReindexing.toTarget C.val (fun s => vertex C (a s)) ≫ F.val := by
  refine EnrichedFunctor.ext SSet.{u} (fun s => ?_) ?_
  · change vertex D (a ((LabelRestriction.map a F).val.obj s)) = F.val.obj (vertex C (a s))
    exact (congrArg (fun t : A => vertex D (a t)) (LabelRestriction.map_obj a F s)).trans
      (map_vertex F (a s)).symm
  · intro s t
    let hb : hom D (a s) (a t) =
        (F.val.obj (vertex C (a s)) ⟶[SSet.{u}] F.val.obj (vertex C (a t))) := by
      rw [map_vertex F (a s), map_vertex F (a t)]
    change ((LabelRestriction.map a F).val.map s t ≫ 𝟙 (hom D (a s) (a t))) ≫ eqToHom hb =
      𝟙 (hom C (a s) (a t)) ≫ F.val.map (vertex C (a s)) (vertex C (a t))
    simp only [Category.id_comp]
    have hh : homMap F (a s) (a t) ≫ eqToHom hb =
        F.val.map (vertex C (a s)) (vertex C (a t)) := by
      unfold homMap
      rw [Category.assoc, eqToHom_trans]
      simp only [eqToHom_refl, Category.comp_id]
    exact (congrArg (fun k : hom C (a s) (a t) ⟶ hom D (a s) (a t) => k ≫ eqToHom hb)
      (restricted_val_map a F s t)).trans hh

variable {O : Type u}

/-- The actual fixed-target-label path source of the original changing-object enrichment. -/
abbrev object (C : Carrier.{u}) (a : C → O) : FixedObjects O :=
  LabelPushforward.object a (CarrierReindexing.source C)

/-- The whole changing-object generator unit has the original prescribed object function. -/
def inclusion (C : Carrier.{u}) (a : C → O) : C ⟶ (object C a).val :=
  (LabelPushforward.unit a (CarrierReindexing.source C)).val ≫
    CarrierReindexing.toTarget (object C a).val (fun s => vertex (object C a) (a s))

/-- The original individual object maps to the same prescribed target label. -/
theorem inclusion_obj (C : Carrier.{u}) (a : C → O) (x : C) :
    (inclusion C a).obj x = vertex (object C a) (a x) := rfl

/-- The entire original Hom maps by the same path-generator inclusion. -/
theorem inclusion_map (C : Carrier.{u}) (a : C → O) (x y : C) :
    (inclusion C a).map x y = LabelPushforward.unitHom a (CarrierReindexing.source C) x y := by
  change (𝟙 (hom (CarrierReindexing.source C) x y) ≫
    LabelPushforward.unitHom a (CarrierReindexing.source C) x y) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

end CategoryTheory.SimplicialEnrichment.CarrierLabelExtension
