/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFrameHom
import MathlibExt.AlgebraicTopology.SimplicialObject.CoefficientReedyMorphismPropertyTransport
import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyModelCategory
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanHomRestriction
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RelativeMatchingTrivialFibration
import Mathlib.AlgebraicTopology.ModelCategory.Opposite

/-!
# Actual trivial-fibration preservation by original Hom complexes

Coefficient Yoneda preserves the full relative matching pullbacks and
matching limits. Genuine opposite-coefficient trivial fibrations give
surjective Hom restrictions into the supplied Kan complex; the actual
boundary lifting criterion then gives a whole Kan–Quillen trivial
fibration of the original Hom complexes.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen CategoryTheory.SimplicialObject.reedyModelCategory

namespace CategoryTheory.CoherentRealization.FrameHom

/-- Every actual relative matching map of the same original Hom-complex map is epimorphic under a genuine
  source Reedy trivial fibration. -/
theorem relativeMatching_epimorphism (H : SSet.{u}) [SSet.KanComplex H]
    {X Y : SimplicialObject (SSet.{u}ᵒᵖ)} (f : X ⟶ Y)
    (hf : trivialFibrations (SimplicialObject (SSet.{u}ᵒᵖ)) f) (n : ℕ) :
    MorphismProperty.epimorphisms (Type u)
      (SimplicialObject.relativeMatchingMap ((functor H).map f) n) := by
  have h : SimplicialObject.reedyRight (trivialFibrations (SSet.{u}ᵒᵖ)) f := by
    rw [SimplicialObject.reedyRight_trivialFibrations_eq]
    exact hf
  apply (SimplicialObject.CoefficientReedyTransport.relativeMatching_mem_iff
    (yoneda.obj H) (MorphismProperty.epimorphisms (Type u)) n f).mp
  exact (CategoryTheory.epi_iff_surjective _).mpr
    (SSet.KanHomRestriction.coefficient_surjective H
      (SimplicialObject.relativeMatchingMap f n) (h n))

/-- The actual original Hom-complex functor into a Kan complex preserves genuine Reedy trivial fibrations. -/
theorem map_trivialFibration (H : SSet.{u}) [SSet.KanComplex H]
    {X Y : SimplicialObject (SSet.{u}ᵒᵖ)} (f : X ⟶ Y)
    (hf : trivialFibrations (SimplicialObject (SSet.{u}ᵒᵖ)) f) :
    trivialFibrations SSet.{u} ((functor H).map f) :=
  SSet.modelCategoryQuillen.trivialFibration_of_relativeMatching_epimorphisms
    ((functor H).map f) (relativeMatching_epimorphism H f hf)

end CategoryTheory.CoherentRealization.FrameHom
