/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFilteredColimits
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Same-object Hom anodyne maps and actual transfinite closure

Every individual original Hom map is tested in the scalar Kan model.
The proved fixed-object Hom colimit preservation applies to the entire
well-ordered sequence and to each genuine nonempty limit initial segment.
It therefore proves actual same-object transfinite anodyne closure.
No preservation of arbitrary enriched coproducts is asserted here.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable (O : Type u)

/-- The actual scalar anodyne property on every original fixed-label Hom map. -/
def homAnodyne : MorphismProperty (FixedObjects O) :=
  ⨅ x : O, ⨅ y : O, SSet.anodyneExtensions.inverseImage (evaluation x y)

variable {O}

/-- Membership tests the entire original Hom map at every same individual label pair. -/
theorem homAnodyne_iff {C D : FixedObjects O} (f : C ⟶ D) :
    homAnodyne O f ↔ ∀ x y : O, SSet.anodyneExtensions (homMap f x y) := by
  simp only [homAnodyne, MorphismProperty.iInf_iff]
  rfl

/-- The label test is equivalent to the scalar anodyne test on all original vertices and whole Hom maps. -/
theorem homAnodyne_original_iff {C D : FixedObjects O} (f : C ⟶ D) :
    homAnodyne O f ↔ ∀ a b : C.val, SSet.anodyneExtensions (f.val.map a b) :=
  (homAnodyne_iff f).trans (all_homMap_property_iff SSet.anodyneExtensions f)

instance homAnodyne_respectsIso : (homAnodyne O).RespectsIso := by
  dsimp only [homAnodyne]
  infer_instance

instance homAnodyne_multiplicative : (homAnodyne O).IsMultiplicative := by
  dsimp only [homAnodyne]
  infer_instance

instance homAnodyne_retracts : (homAnodyne O).IsStableUnderRetracts where
  of_retract h hg := by
    rw [homAnodyne_iff] at hg ⊢
    intro x y
    exact MorphismProperty.of_retract (P := SSet.anodyneExtensions) (h.map (evaluation x y)) (hg x y)

/-- Hom evaluation preserves the actual nonempty initial-segment colimits at every genuine limit stage. -/
instance evaluationWellOrderContinuous {J : Type u} [LinearOrder J] (x y : O) :
    PreservesWellOrderContinuousOfShape J (evaluation x y) where
  preservesColimitsOfShape j hj := by
    have : Nonempty (Set.Iio j) := by
      by_contra h
      apply hj.1
      intro i _hij
      by_contra hji
      exact h ⟨⟨i, lt_of_not_ge hji⟩⟩
    have : IsFiltered (Set.Iio j) := inferInstance
    infer_instance

/-- Every actual supported transfinite composite retains anodyne weakness on its whole original Homs. -/
instance homAnodyne_transfiniteShape {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J]
    [WellFoundedLT J] : (homAnodyne O).IsStableUnderTransfiniteCompositionOfShape J where
  le := by
    intro C D f hf
    obtain ⟨h⟩ := hf
    rw [homAnodyne_iff]
    intro x y
    let hx : (SSet.anodyneExtensions.inverseImage (evaluation x y)).TransfiniteCompositionOfShape J f := {
      __ := h.toTransfiniteCompositionOfShape
      map_mem j hj := (homAnodyne_iff _).mp (h.map_mem j hj) x y }
    let he := hx.map
    exact SSet.anodyneExtensions.transfiniteCompositionsOfShape_le J _
      (MorphismProperty.TransfiniteCompositionOfShape.mem _ he)

/-- The same whole original Hom property is stable through supported small transfinite composites. -/
instance homAnodyne_transfinite : (homAnodyne O).IsStableUnderTransfiniteComposition.{u} where
  isStableUnderTransfiniteCompositionOfShape _J _ _ _ _ := inferInstance

end CategoryTheory.SimplicialEnrichment.FixedObjects
