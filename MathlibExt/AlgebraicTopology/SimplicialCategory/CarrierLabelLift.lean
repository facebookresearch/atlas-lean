/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLabelUniversalProperty
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLabelReadback

/-! # Genuine whole enriched extension along an arbitrary original label map

An actual source functor whose object function factors through the
specified labels extends to the original path source. All original Hom
maps and the whole source functor are retained. The extension is unique
with its prescribed target object function, including noninjective maps.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.CarrierLabelLift
open FixedObjects CarrierLabelExtension CarrierLabelUniversalProperty

/-- The two original identity-Hom reindexing projections compose to their same object function. -/
theorem projection_comp {A O : Type u} (a : A → O) {D : Carrier.{u}} (b : O → D) :
    CarrierReindexing.toTarget (CarrierReindexing.object D b).val a ≫
      CarrierReindexing.toTarget D b = CarrierReindexing.toTarget D (fun x => b (a x)) := by
  refine EnrichedFunctor.ext SSet.{u}
    (F := CarrierReindexing.toTarget (CarrierReindexing.object D b).val a ≫
      CarrierReindexing.toTarget D b)
    (G := CarrierReindexing.toTarget D (fun x => b (a x))) (fun _ => rfl) ?_
  intro x y
  change (𝟙 (b (a x) ⟶[SSet.{u}] b (a y)) ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _
  simp

variable (C : Carrier.{u}) {O : Type u} (a : C → O) {D : Carrier.{u}}
variable (b : O → D)

/-- Projecting the complete original unit through both label rows retains the whole target
functor. -/
theorem unit_target_projection (G : object C a ⟶ CarrierReindexing.object D b) :
    (LabelPushforward.unit a (CarrierReindexing.source C) ≫ LabelRestriction.map a G).val ≫
      CarrierReindexing.toTarget D (fun x => b (a x)) =
        inclusion C a ≫ (G.val ≫ CarrierReindexing.toTarget D b) := by
  let U := LabelPushforward.unit a (CarrierReindexing.source C) ≫ LabelRestriction.map a G
  change U.val ≫ CarrierReindexing.toTarget D (fun x => b (a x)) = _
  exact (congrArg (fun k => U.val ≫ k) (projection_comp a b).symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ CarrierReindexing.toTarget D b) (unit_projection C a G)).trans
        (Category.assoc _ _ _)))

variable (F : C ⟶ D) (h : F.obj = fun x => b (a x))

/-- The actual original source functor as a fixed-source map through the two prescribed
label rows. -/
def fixedInput : CarrierReindexing.source C ⟶
    LabelRestriction.object a (CarrierReindexing.object D b) :=
  CarrierLabelMaps.ofObjectEquation (fun x => b (a x)) F h

/-- The genuine fixed-target-label extension of the actual source functor. -/
def fixedLift : object C a ⟶ CarrierReindexing.object D b :=
  LabelPushforward.desc a (CarrierReindexing.source C) (fixedInput C a b F h)

/-- The whole enriched functor on the original target labels, constructed from the actual source. -/
def lift : (object C a).val ⟶ D :=
  (fixedLift C a b F h).val ≫ CarrierReindexing.toTarget D b

/-- Every target label maps to its same prescribed individual object. -/
theorem lift_obj (x : O) : (lift C a b F h).obj x = b x := by
  change b ((fixedLift C a b F h).val.obj x) = b x
  have hx := map_vertex (fixedLift C a b F h) x
  change (fixedLift C a b F h).val.obj x = x at hx
  exact congrArg b hx

/-- The constructed extension retains the entire original source enriched functor. -/
theorem lift_fac : inclusion C a ≫ lift C a b F h = F := by
  have hu := congrArg
    (fun H : CarrierReindexing.source C ⟶ LabelRestriction.object a
      (CarrierReindexing.object D b) =>
      H.val ≫ CarrierReindexing.toTarget D (fun x => b (a x)))
    (LabelPushforward.unit_desc a (CarrierReindexing.source C) (fixedInput C a b F h))
  exact (unit_target_projection C a b (fixedLift C a b F h)).symm.trans
    (hu.trans (CarrierLabelMaps.ofObjectEquation_fac (fun x => b (a x)) F h))

/-- Any whole extension with the same target objects and original source functor is the
constructed extension. -/
theorem lift_unique (H : (object C a).val ⟶ D) (hH : H.obj = b)
    (hF : inclusion C a ≫ H = F) : H = lift C a b F h := by
  let G : object C a ⟶ CarrierReindexing.object D b :=
    CarrierLabelReadback.map (object C a) b H (fun x => congrFun hH x)
  have hG : G.val ≫ CarrierReindexing.toTarget D b = H :=
    CarrierLabelReadback.map_fac (object C a) b H (fun x => congrFun hH x)
  have hu : LabelPushforward.unit a (CarrierReindexing.source C) ≫
      LabelRestriction.map a G = fixedInput C a b F h := by
    apply CarrierLabelMaps.projection_injective (fun x => b (a x))
    exact (unit_target_projection C a b G).trans
      ((congrArg (fun k => inclusion C a ≫ k) hG).trans
        (hF.trans (CarrierLabelMaps.ofObjectEquation_fac (fun x => b (a x)) F h).symm))
  have hg : G = fixedLift C a b F h :=
    LabelPushforward.desc_unique a (CarrierReindexing.source C) (fixedInput C a b F h) G hu
  exact hG.symm.trans
    (congrArg (fun k : object C a ⟶ CarrierReindexing.object D b =>
      k.val ≫ CarrierReindexing.toTarget D b) hg)

end CategoryTheory.SimplicialEnrichment.CarrierLabelLift
