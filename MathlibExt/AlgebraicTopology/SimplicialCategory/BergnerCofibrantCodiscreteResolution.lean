/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerFixedInitialObjects
import MathlibExt.AlgebraicTopology.SimplicialCategory.CodiscreteComponentIsomorphisms
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectCodiscreteTerminal
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectModel
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedDwyerKanClasses

/-!
# Actual cofibrant resolution of the original unit-Hom enrichment

The genuine fixed-label boundary small-object construction resolves the
original codiscrete enrichment on its SAME individual labels. Its full
original Hom projections are scalar trivial fibrations, so every original
resolved Hom is Kan and weakly contractible. The actual initial-point
cofibration and full boundary left leg make every original selected point
globally C0 cofibrant. Its SAME unit Hom and component isomorphisms prove
that selected point map is genuinely DK weak. No countability, arbitrary
interval lifting or global enriched model/QE outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.BergnerCofibrantCodiscreteResolution
open FixedObjects

/-- The SAME original codiscrete unit-Hom target on its supplied individual labels. -/
abbrev target (O : Type u) : FixedObjects O := CodiscreteTerminal.object O

/-- The actual original fixed-label initial map to that SAME original unit-Hom target. -/
def input (O : Type u) : BergnerFixedInitialObjects.fixedObject O ⟶ target O := initial.to _

/-- The genuine stored original free-boundary small-object factorization. -/
abbrev factorization (O : Type u) := FreeFactorization.boundary (input O)

/-- The actual resolved original fixed-label enrichment. -/
abbrev fixedObject (O : Type u) : FixedObjects O := (factorization O).Z

/-- Its SAME whole changing-object original carrier. -/
abbrev object (O : Type u) : Carrier.{u} := (fixedObject O).val

/-- The SAME actual full original boundary left leg. -/
abbrev left (O : Type u) := (factorization O).i

/-- The SAME actual full original unit-Hom projection. -/
abbrev right (O : Type u) := (factorization O).p

/-- Every supplied individual original label retains its actual resolved vertex. -/
def vertex (O : Type u) (x : O) : object O := FixedObjects.vertex (fixedObject O) x

/-- The actual two whole original fixed-label maps recover the SAME original initial-to-unit map. -/
theorem fac (O : Type u) : left O ≫ right O = input O := (factorization O).fac

/-- Every full original resolved Hom projection is a genuine scalar trivial fibration. -/
theorem right_homs (O : Type u) (a b : object O) :
    Fibration ((right O).val.map a b) ∧ SSet.realizationWeakEquivalences ((right O).val.map a b) :=
  FreeFactorization.boundary_p_original (input O) a b

/-- The SAME entire original changing-object projection is genuinely DK weak. -/
theorem right_weak (O : Type u) : EnrichedDwyerKan.weakEquivalences (right O).val :=
  (EnrichedDwyerKan.fixedWeak_iff (right O)).mpr
    ((FixedObjectModel.weakEquivalences_original_iff (right O)).mpr
      (fun a b => (right_homs O a b).2))

/-- Every actual original resolved Hom is Kan through its SAME full scalar unit projection. -/
theorem homKan (O : Type u) (a b : object O) : SSet.KanComplex (a ⟶[SSet.{u}] b) := by
  let _ : Fibration ((right O).val.map a b) := (right_homs O a b).1
  let _ : SSet.KanComplex ((right O).val.obj a ⟶[SSet.{u}] (right O).val.obj b) := by
    change SSet.KanComplex (𝟙_ SSet.{u})
    exact (isFibrant_iff_of_isTerminal (𝟙 (𝟙_ SSet.{u}))
      (CartesianMonoidalCategory.isTerminalTensorUnit : IsTerminal (𝟙_ SSet.{u}))).mpr (by infer_instance)
  exact isFibrant_of_fibration ((right O).val.map a b)

/-- The actual resolved fixed-label object is cofibrant in the SAME original fixed-object model. -/
theorem fixed_cofibrant (O : Type u) :
    let _ : ModelCategory (FixedObjects O) := FixedObjectModel.modelCategory O
    IsCofibrant (fixedObject O) := by
  dsimp only
  let _ : ModelCategory (FixedObjects O) := FixedObjectModel.modelCategory O
  have hi : Cofibration (left O) :=
    (FixedObjectModel.cofibration_iff_freeBoundary (left O)).mpr (factorization O).hi
  have h : initial.to (fixedObject O) = left O := initialIsInitial.hom_ext _ _
  exact (congrArg (fun F : BergnerFixedInitialObjects.fixedObject O ⟶ fixedObject O => Cofibration F) h).mpr hi

/-- The SAME full original boundary left leg is genuinely globally C0 cofibrant. -/
theorem left_cofibration (O : Type u) : Bergner.cofibrations (left O).val :=
  Bergner.fixedCofibration_global (left O) (factorization O).hi

/-- Every original selected point retains its actual initial vertex and whole boundary map. -/
theorem point_original_factor (O : Type u) (x : O) :
    BergnerObjects.select (BergnerFixedInitialObjects.vertex O x) ≫ (left O).val =
      BergnerObjects.select (vertex O x) :=
  (BergnerObjects.select_comp (BergnerFixedInitialObjects.vertex O x) (left O).val).trans
    (congrArg BergnerObjects.select (map_vertex (left O) x))

/-- The SAME actual resolved point inclusion is a genuine global C0 cofibration. -/
theorem point_cofibration (O : Type u) (x : O) : Bergner.cofibrations (BergnerObjects.select (vertex O x)) :=
  (congrArg (fun F : BergnerObjects.point.{u} ⟶ object O => Bergner.cofibrations F)
    (point_original_factor O x)).mp
      (Bergner.cofibrations.comp_mem _ _ (BergnerFixedInitialObjects.point_cofibration O x)
        (left_cofibration O))

/-- The SAME original identity unit-Hom map is weak by its actual full projection triangle. -/
theorem identityHom_weak (O : Type u) (a : object O) :
    SSet.realizationWeakEquivalences (eId SSet.{u} a) := by
  have h : eId SSet.{u} a ≫ (right O).val.map a a = 𝟙 (𝟙_ SSet.{u}) := (right O).val.map_id a
  have hcomp : SSet.realizationWeakEquivalences (eId SSet.{u} a ≫ (right O).val.map a a) :=
    (congrArg (fun f : (𝟙_ SSet.{u}) ⟶ (𝟙_ SSet.{u}) => SSet.realizationWeakEquivalences f) h).mpr
      (SSet.realizationWeakEquivalences.id_mem _)
  exact SSet.realizationWeakEquivalences.of_postcomp _ _ (right_homs O a a).2 hcomp

/-- Every SAME pair of original resolved objects has an actual component isomorphism lifted through its original
full Hom projection. -/
def componentIso (O : Type u) (a b : object O) :
    ComponentCategory.objectOf.{u} (object O) a ≅ ComponentCategory.objectOf.{u} (object O) b :=
  (EnrichedDwyerKan.componentFullyFaithful (right O).val (right_weak O).1).preimageIso
    (CodiscreteComponentIsomorphisms.iso O ((right O).val.obj a) ((right O).val.obj b))

/-- The SAME actual selected point map is genuinely weak on its original unit Hom and original component objects. -/
theorem point_weak (O : Type u) (x : O) : EnrichedDwyerKan.weakEquivalences (BergnerObjects.select (vertex O x)) := by
  constructor
  · intro a b
    exact identityHom_weak O (vertex O x)
  · refine ⟨fun y => ?_⟩
    exact ⟨PUnit.unit, ⟨componentIso O (vertex O x) (ComponentCategory.originalObject (object O) y)⟩⟩

/-- Both genuine global properties hold for the SAME actual resolved original point map. -/
theorem point_cofibration_and_weak (O : Type u) (x : O) :
    (Bergner.cofibrations ⊓ EnrichedDwyerKan.weakEquivalences) (BergnerObjects.select (vertex O x)) :=
  ⟨point_cofibration O x, point_weak O x⟩

end CategoryTheory.SimplicialEnrichment.BergnerCofibrantCodiscreteResolution
