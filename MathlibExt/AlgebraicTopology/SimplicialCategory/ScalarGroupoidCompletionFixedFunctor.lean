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
# The SAME native canonical completion on original fixed-label enrichments

The actual full completion object retains the original fixed-label
object equality. Its SAME original completion map and unit become
genuine arrows of the original fibre by their actual original object
functions. Whole identity, composition and unit naturality remain the
same original enriched maps, with no weak comparison premise.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion
open FixedObjects

variable {O : Type u}

/-- The SAME actual canonical completion retains its original fixed-label object equality. -/
def fixedObject (C : FixedObjects O) : FixedObjects O := ⟨object C.val, C.property⟩

/-- The SAME entire original canonical completion map lifts to the actual original object fibre. -/
def fixedMap {C D : FixedObjects O} (F : C ⟶ D) : fixedObject C ⟶ fixedObject D := by
  refine ⟨map F.val, ?_⟩
  apply IsHomLift.of_fac' forgetObjects (𝟙 O) (map F.val) (fixedObject C).property
    (fixedObject D).property
  have : forgetObjects.IsHomLift (𝟙 O) F.val := F.property
  have h := IsHomLift.fac' forgetObjects (𝟙 O) F.val
  exact h

/-- The SAME actual full original completion unit is a genuine fixed-label arrow. -/
def fixedUnit (C : FixedObjects O) : C ⟶ fixedObject C := by
  rcases C with ⟨C, hC⟩
  cases hC
  refine ⟨unit C, ?_⟩
  apply IsHomLift.of_fac' forgetObjects (𝟙 _) (unit C) rfl rfl
  ext x
  rfl

/-- Every original fixed label retains the SAME actual native completed object under its
whole map. -/
theorem fixedMap_val {C D : FixedObjects O} (F : C ⟶ D) : (fixedMap F).val = map F.val := rfl

/-- The entire fixed unit reads back to the SAME actual original raw native unit. -/
theorem fixedUnit_val (C : FixedObjects O) : (fixedUnit C).val = unit C.val := by
  rcases C with ⟨C, hC⟩
  cases hC
  rfl

/-- The SAME complete original fixed completion map preserves the whole identity. -/
theorem fixedMap_id (C : FixedObjects O) : fixedMap (𝟙 C) = 𝟙 (fixedObject C) := by
  apply Functor.Fiber.hom_ext
  exact map_id C.val

/-- The actual full fixed completion map retains both SAME original maps under composition. -/
theorem fixedMap_comp {C D E : FixedObjects O} (F : C ⟶ D) (G : D ⟶ E) :
    fixedMap (F ≫ G) = fixedMap F ≫ fixedMap G := by
  apply Functor.Fiber.hom_ext
  exact map_comp F.val G.val

/-- The SAME native whole completion functor on the actual original fixed-label fibre. -/
def fixedFunctor : FixedObjects O ⥤ FixedObjects O where
  obj := fixedObject
  map := fixedMap
  map_id := fixedMap_id
  map_comp := fixedMap_comp

/-- The actual fixed original unit square is the SAME whole raw enriched unit square. -/
theorem fixedUnit_naturality {C D : FixedObjects O} (F : C ⟶ D) :
    fixedUnit C ≫ fixedMap F = F ≫ fixedUnit D := by
  apply Functor.Fiber.hom_ext
  exact (congrArg (fun m => m ≫ map F.val) (fixedUnit_val C)).trans
    ((unit_naturality F.val).trans (congrArg (fun m => F.val ≫ m) (fixedUnit_val D)).symm)

/-- The SAME actual original unit is a genuine natural transformation of the full original
fixed-label category. -/
def fixedNaturalUnit : 𝟭 (FixedObjects O) ⟶ fixedFunctor where
  app := fixedUnit
  naturality _ _ F := (fixedUnit_naturality F).symm

end CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion
