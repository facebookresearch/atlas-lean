/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarGroupoidCompletionFunctor
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHomMaps

/-!
# Groupoid completion on fixed-object enrichments

Degreewise groupoid completion defines a functor on enrichments with
fixed object set. Its maps and unit preserve those object labels and
commute with all simplicial operators.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion
open FixedObjects

variable {O : Type u}

/-- The same canonical completion retains its fixed-label object equality. -/
def fixedObject (C : FixedObjects O) : FixedObjects O := ⟨object C.val, C.property⟩

/-- The same canonical completion map lifts to the object fibre. -/
def fixedMap {C D : FixedObjects O} (F : C ⟶ D) : fixedObject C ⟶ fixedObject D := by
  refine ⟨map F.val, ?_⟩
  apply IsHomLift.of_fac' forgetObjects (𝟙 O) (map F.val) (fixedObject C).property
    (fixedObject D).property
  have : forgetObjects.IsHomLift (𝟙 O) F.val := F.property
  have h := IsHomLift.fac' forgetObjects (𝟙 O) F.val
  exact h

/-- The same full completion unit is a fixed-label arrow. -/
def fixedUnit (C : FixedObjects O) : C ⟶ fixedObject C := by
  rcases C with ⟨C, hC⟩
  cases hC
  refine ⟨unit C, ?_⟩
  apply IsHomLift.of_fac' forgetObjects (𝟙 _) (unit C) rfl rfl
  ext x
  rfl

/-- Every fixed label retains the same native completed object under its
map. -/
theorem fixedMap_val {C D : FixedObjects O} (F : C ⟶ D) : (fixedMap F).val = map F.val := rfl

/-- The fixed unit reads back to the same raw native unit. -/
theorem fixedUnit_val (C : FixedObjects O) : (fixedUnit C).val = unit C.val := by
  rcases C with ⟨C, hC⟩
  cases hC
  rfl

/-- The same complete fixed completion map preserves the identity. -/
theorem fixedMap_id (C : FixedObjects O) : fixedMap (𝟙 C) = 𝟙 (fixedObject C) := by
  apply Functor.Fiber.hom_ext
  exact map_id C.val

/-- The full fixed completion map retains both same maps under composition. -/
theorem fixedMap_comp {C D E : FixedObjects O} (F : C ⟶ D) (G : D ⟶ E) :
    fixedMap (F ≫ G) = fixedMap F ≫ fixedMap G := by
  apply Functor.Fiber.hom_ext
  exact map_comp F.val G.val

/-- The same native completion functor on the fixed-label fibre. -/
def fixedFunctor : FixedObjects O ⥤ FixedObjects O where
  obj := fixedObject
  map := fixedMap
  map_id := fixedMap_id
  map_comp := fixedMap_comp

/-- The fixed unit square is the same raw enriched unit square. -/
theorem fixedUnit_naturality {C D : FixedObjects O} (F : C ⟶ D) :
    fixedUnit C ≫ fixedMap F = F ≫ fixedUnit D := by
  apply Functor.Fiber.hom_ext
  exact (congrArg (fun m => m ≫ map F.val) (fixedUnit_val C)).trans
    ((unit_naturality F.val).trans (congrArg (fun m => F.val ≫ m) (fixedUnit_val D)).symm)

/-- The same unit is a natural transformation of the full 
fixed-label category. -/
def fixedNaturalUnit : 𝟭 (FixedObjects O) ⟶ fixedFunctor where
  app := fixedUnit
  naturality _ _ F := (fixedUnit_naturality F).symm

end CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion
