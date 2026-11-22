/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeSingleHomLifting
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabels
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPRealizationWeakEquivalence

/-!
# Free boundaries and horns detect the original enriched Hom maps

The actual fixed-object free generators recognize scalar Kan fibrations
and scalar trivial fibrations on every original Hom. No model structure
on simplicial enriched categories is supplied or inferred.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable {O : Type u}

/-- Actual free boundary inclusions at all original ordered pairs, including loop pairs. -/
abbrev boundaryGenerators : MorphismProperty (FixedObjects O) :=
  freeGenerators SSet.modelCategoryQuillen.I

/-- Actual free positive-dimensional horn inclusions at all original ordered pairs. -/
abbrev hornGenerators : MorphismProperty (FixedObjects O) :=
  freeGenerators SSet.modelCategoryQuillen.J

/-- Free horn RLP is precisely scalar fibration of every evaluated original Hom map. -/
theorem hornGenerators_rlp_iff {C D : FixedObjects O} (p : C ⟶ D) :
    hornGenerators.rlp p ↔ ∀ x y : O, Fibration (homMap p x y) := by
  rw [freeGenerators_rlp_iff]
  exact forall_congr' fun x => forall_congr' fun y =>
    (SSet.modelCategoryQuillen.fibration_iff _).symm

/-- The same free horn criterion detects every Hom between actual original vertices. -/
theorem hornGenerators_rlp_iff_original {C D : FixedObjects O} (p : C ⟶ D) :
    hornGenerators.rlp p ↔ ∀ a b : C.val, Fibration (p.val.map a b) := by
  rw [freeGenerators_rlp_iff, all_homMap_property_iff]
  exact forall_congr' fun a => forall_congr' fun b =>
    (SSet.modelCategoryQuillen.fibration_iff _).symm

private theorem scalar_boundary_iff {X Y : SSet.{u}} (p : X ⟶ Y) :
    SSet.modelCategoryQuillen.I.rlp p ↔
      Fibration p ∧ SSet.realizationWeakEquivalences p := by
  constructor
  · intro hp
    have hm : (MorphismProperty.monomorphisms SSet.{u}).rlp p := by
      rwa [SSet.rlp_monomorphisms]
    have hJ := MorphismProperty.antitone_rlp SSet.modelCategoryQuillen.J_le_monomorphisms p hm
    have hf := (SSet.modelCategoryQuillen.fibration_iff p).mpr hJ
    have : Fibration p := hf
    exact ⟨hf, (SSet.modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration p).mp hp⟩
  · rintro ⟨hf, hw⟩
    have : Fibration p := hf
    exact (SSet.modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration p).mpr hw

/-- Free boundary RLP is precisely actual scalar trivial fibration on every original Hom. -/
theorem boundaryGenerators_rlp_iff {C D : FixedObjects O} (p : C ⟶ D) :
    boundaryGenerators.rlp p ↔ ∀ x y : O,
      Fibration (homMap p x y) ∧ SSet.realizationWeakEquivalences (homMap p x y) := by
  rw [freeGenerators_rlp_iff]
  exact forall_congr' fun x => forall_congr' fun y => scalar_boundary_iff _

/-- The boundary criterion retains every individual original endpoint and its entire Hom map. -/
theorem boundaryGenerators_rlp_iff_original {C D : FixedObjects O} (p : C ⟶ D) :
    boundaryGenerators.rlp p ↔ ∀ a b : C.val,
      Fibration (p.val.map a b) ∧ SSet.realizationWeakEquivalences (p.val.map a b) := by
  rw [freeGenerators_rlp_iff, all_homMap_property_iff]
  exact forall_congr' fun a => forall_congr' fun b => scalar_boundary_iff _

end CategoryTheory.SimplicialEnrichment.FixedObjects
