/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjects

/-!
# Actual enriched targets reindexed along original object functions

The new target has the literal supplied original label type and the
actual target Homs at their specified images. Every whole changing-object
enriched map factors through this fixed-object target. Its original Hom
maps and both complete-map factorization equations are unchanged.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.CarrierReindexing

variable {O : Type u}

/-- The actual target enrichment on the supplied original labels and their specified images. -/
@[instance_reducible]
def enrichment (D : Carrier.{u}) (a : O → D) : EnrichedCategory SSet.{u} O where
  Hom x y := a x ⟶[SSet.{u}] a y
  id x := eId SSet.{u} (a x)
  comp x y z := eComp SSet.{u} (a x) (a y) (a z)
  id_comp x y := e_id_comp SSet.{u} (a x) (a y)
  comp_id x y := e_comp_id SSet.{u} (a x) (a y)
  assoc w x y z := e_assoc SSet.{u} (a w) (a x) (a y) (a z)

/-- Bundle the genuine reindexed target in the actual original fixed-object fiber. -/
def object (D : Carrier.{u}) (a : O → D) : FixedObjects O := by
  let _ : EnrichedCategory SSet.{u} O := enrichment D a
  exact FixedObjects.of O

/-- Every source label remains that exact individual label in the reindexed target. -/
theorem object_vertex (D : Carrier.{u}) (a : O → D) (x : O) :
    FixedObjects.vertex (object D a) x = x := rfl

/-- The reindexed Hom is the same literal original target Hom at the two supplied images. -/
theorem object_hom (D : Carrier.{u}) (a : O → D) (x y : O) :
    FixedObjects.hom (object D a) x y = (a x ⟶[SSet.{u}] a y) := rfl

/-- The actual projection to the original target has the specified object function and
identity Hom maps. -/
def toTarget (D : Carrier.{u}) (a : O → D) : (object D a).val ⟶ D where
  obj := a
  map _ _ := 𝟙 _
  map_id _ := Category.comp_id _
  map_comp x y z := by
    change (𝟙 _ ⊗ₘ 𝟙 _) ≫ eComp SSet.{u} (a x) (a y) (a z) =
      eComp SSet.{u} (a x) (a y) (a z) ≫ 𝟙 _
    simp

/-- The original target projection reads each supplied label to its specified individual image. -/
theorem toTarget_obj (D : Carrier.{u}) (a : O → D) (x : O) : (toTarget D a).obj x = a x := rfl

/-- The whole original target Hom map of the projection is exactly its identity. -/
theorem toTarget_map (D : Carrier.{u}) (a : O → D) (x y : O) :
    (toTarget D a).map x y = 𝟙 (a x ⟶[SSet.{u}] a y) := rfl

/-- The unchanged original source as an object of the fiber over its individual objects. -/
abbrev source (C : Carrier.{u}) : FixedObjects (C : Type u) := ⟨C, rfl⟩

/-- The supplied whole enriched map as an actual fixed-object map into its reindexed target. -/
def fixedPart {C D : Carrier.{u}} (F : C ⟶ D) : source C ⟶ object D F.obj := by
  let G : EnrichedFunctor SSet.{u} C (object D F.obj).val :=
    { obj x := x
      map x y := F.map x y
      map_id x := F.map_id x
      map_comp x y z := F.map_comp x y z }
  refine ⟨G, ?_⟩
  apply IsHomLift.of_fac' forgetObjects (𝟙 (C : Type u)) G rfl (object D F.obj).property
  ext x
  rfl

/-- The fixed part retains each original source object literally. -/
theorem fixedPart_obj {C D : Carrier.{u}} (F : C ⟶ D) (x : C) : (fixedPart F).val.obj x = x := rfl

/-- The fixed part has exactly the same whole original enriched Hom map. -/
theorem fixedPart_homMap {C D : Carrier.{u}} (F : C ⟶ D) (x y : C) :
    FixedObjects.homMap (fixedPart F) x y = F.map x y := by
  change F.map x y ≫ eqToHom _ = F.map x y
  simp

/-- The whole original changing-object enriched functor is recovered, including every Hom map. -/
theorem factorization {C D : Carrier.{u}} (F : C ⟶ D) :
    (fixedPart F).val ≫ toTarget D F.obj = F := by
  apply EnrichedFunctor.ext SSet.{u} (F := (fixedPart F).val ≫ toTarget D F.obj) (G := F)
    (fun _ => rfl)
  intro x y
  change F.map x y ≫ 𝟙 _ = F.map x y
  simp


end CategoryTheory.SimplicialEnrichment.CarrierReindexing
