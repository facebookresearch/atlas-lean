/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerFreeObjects
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerFixedObjectGlobalLifting

/-!
# The actual changing-object addition stage

For every original enriched functor F:C→D, take the genuine coproduct
C plus one original unit-Hom object for EVERY individual target object.
Its actual augmentation retains F on the entire original C summand and
evaluates the new summands at those same D objects. It is literally
surjective on objects. The left injection lifts against every arbitrary
original map surjective on objects, hence lies in the genuine global
C0 left class. No desired global model outcome is supplied.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.BergnerObjectAddition

variable {C D : Carrier.{u}} (F : C ⟶ D)

/-- The actual original source plus the entire free family of individual original target objects. -/
def object (_F : C ⟶ D) : Carrier.{u} := C ⨿ BergnerFreeObjects.object (D : Type u)

/-- The same whole original source coproduct injection. -/
def left : C ⟶ object F := coprod.inl

/-- The actual augmentation is the original F on C and the same original object evaluation on every new summand. -/
def right : object F ⟶ D := coprod.desc F ((BergnerFreeObjects.adjunction.{u}).counit.app D)

/-- The individual original new vertex supplied for the SAME target object. -/
def newVertex (x : D) : object F :=
  (coprod.inr : BergnerFreeObjects.object (D : Type u) ⟶ object F).obj
    (BergnerFreeObjects.vertex (D : Type u) x)

/-- The entire original functor is retained through both actual object-addition maps. -/
theorem fac : left F ≫ right F = F := coprod.inl_desc _ _

/-- The whole original second summand retains the actual free-object counit. -/
theorem right_on_free :
    (coprod.inr : BergnerFreeObjects.object (D : Type u) ⟶ object F) ≫ right F =
      (BergnerFreeObjects.adjunction.{u}).counit.app D := coprod.inr_desc _ _

/-- The augmentation reads every actual new vertex to its SAME original target object. -/
theorem right_newVertex (x : D) : (right F).obj (newVertex F x) = x := by
  have hx := congrArg (fun G : BergnerFreeObjects.object (D : Type u) ⟶ D =>
    G.obj (BergnerFreeObjects.vertex (D : Type u) x)) (right_on_free F)
  exact hx.trans (BergnerFreeObjects.desc_vertex (D : Type u) id x)

/-- The actual object-addition augmentation covers EVERY original target object literally. -/
theorem right_objects_surjective : Function.Surjective (right F).obj :=
  fun x => ⟨newVertex F x, right_newVertex F x⟩

/-- The whole original object-addition injection lifts against any actual surjective original object map. -/
theorem left_hasLiftingProperty {E H : Carrier.{u}} (r : E ⟶ H)
    (hr : Function.Surjective r.obj) : HasLiftingProperty (left F) r := by
  refine ⟨fun {top bottom} sq => ?_⟩
  choose a ha using (fun x : D => hr (bottom.obj (newVertex F x)))
  let freeLift : BergnerFreeObjects.object (D : Type u) ⟶ E :=
    BergnerFreeObjects.desc (D : Type u) a
  let lift : object F ⟶ E := coprod.desc top freeLift
  refine CommSq.HasLift.mk' ⟨lift, coprod.inl_desc _ _, ?_⟩
  apply coprod.hom_ext
  · change (coprod.inl : C ⟶ object F) ≫ (lift ≫ r) = coprod.inl ≫ bottom
    rw [← Category.assoc]
    exact (congrArg (fun k => k ≫ r) (coprod.inl_desc top freeLift)).trans sq.w
  · change (coprod.inr : BergnerFreeObjects.object (D : Type u) ⟶ object F) ≫ (lift ≫ r) =
      coprod.inr ≫ bottom
    rw [← Category.assoc, coprod.inr_desc]
    apply (BergnerFreeObjects.homEquiv (D : Type u) H).injective
    funext x
    change r.obj ((BergnerFreeObjects.desc (D : Type u) a).obj
      (BergnerFreeObjects.vertex (D : Type u) x)) = bottom.obj (newVertex F x)
    rw [BergnerFreeObjects.desc_vertex]
    exact ha x

/-- The actual source injection is a genuine global C0 cofibration on the SAME full enriched map. -/
theorem left_cofibration : Bergner.cofibrations (left F) := by
  intro E H r hr
  exact left_hasLiftingProperty F r ((Bergner.generatingCofibrations_rlp_iff r).mp hr).1

end CategoryTheory.SimplicialEnrichment.BergnerObjectAddition
