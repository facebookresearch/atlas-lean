/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeQuotientCylinder
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceHomotopyInvariance

/-!
# Actual point contraction of the original right-cube quotient

The genuine quotient cylinder contracts the original right cube to its
full interval class. The original tensor-unit projection and its actual
full-path section retain both whole composite maps. This supplies the
concrete homotopy needed for weak contractibility, without a Kan or
resolution-comparison hypothesis.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.CoherentRealization.RightCubePoint
open RightCubeRelations RightCubeQuotientCylinder RightCubeFullPath PathLastMaximum

/-- The actual full original interval class as a whole tensor-unit section of the right-cube quotient. -/
def sectionMap (n : ℕ) : 𝟙_ SSet.{u} ⟶ RightCubeRelations.object.{u} n where
  app q := ↾fun _ => fullClass q
  naturality q r θ := by ext a; congr 1

/-- The actual whole tensor-unit projection of the original right-cube quotient. -/
def projection (n : ℕ) : RightCubeRelations.object.{u} n ⟶ 𝟙_ SSet.{u} := SimplicialEnrichment.toUnit _

/-- The full-path section retains the original unit identity. -/
theorem section_projection (n : ℕ) : sectionMap.{u} n ≫ projection n = 𝟙 (𝟙_ SSet.{u}) := by ext q a; rfl

/-- The projection followed by its section is the actual whole original full-path-class map. -/
theorem projection_section (n : ℕ) : projection.{u} n ≫ sectionMap n = constantMap n := by ext q a; rfl

/-- The original quotient identity and its literal projection-section composite have the actual
  relation-compatible homotopy. -/
def homotopy (n : ℕ) : SSet.Homotopy (𝟙 (RightCubeRelations.object.{u} n)) (projection n ≫ sectionMap n) := by
  have h := RightCubeQuotientCylinder.homotopy.{u} n
  exact (projection_section n).symm ▸ h

/-- The whole original projection-section composite is a realization weak equivalence by the actual quotient
  cylinder. -/
theorem projection_section_weak (n : ℕ) : SSet.realizationWeakEquivalences (projection.{u} n ≫ sectionMap n) :=
  (SSet.realizationWeakEquivalences_iff_of_homotopy (homotopy n)).mp (SSet.realizationWeakEquivalences.of_isIso _)

end CategoryTheory.CoherentRealization.RightCubePoint
