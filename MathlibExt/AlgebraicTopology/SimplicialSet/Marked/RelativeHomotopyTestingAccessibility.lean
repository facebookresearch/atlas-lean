/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeTestingFunctorAccessibility
import MathlibExt.AlgebraicTopology.ModelCategory.AccessibleMorphismProperty
import MathlibExt.CategoryTheory.Presentable.InverseImage
import MathlibExt.CategoryTheory.Presentable.SurjectiveArrow

/-!
# Accessibility of all original relative homotopy weak arrows

The actual all-arrow testing predicate is the inverse image of native
surjective arrows along the proved accessible small lifting functor.
The existing inverse-image accessibility theorem gives a real regular
rank for both the full original arrow category and its inclusion. This
rank is produced from the native functors and differs from their frozen
factor ordinals. The full mapping weak-class identification remains
separate; no bounded-arrow or supplied model outcome is used.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty CategoryTheory.Presentable

namespace SSet.Marked

/-- The actual original Cartesian homotopy weak-arrow predicate equals the same full lifting-test
  surjectivity predicate. -/
theorem cartesianRelativeHomotopyTesting_arrow_inverseImage (B : SSet.{u}) [Quasicategory B] :
    (cartesianRelativeHomotopyTesting B).arrowObjectProperty =
      surjectiveArrows.{u}.inverseImage (cartesianRelativeWeakLiftingTest B) := by
  funext f
  exact propext (cartesianRelativeWeakLiftingTest_surjective_iff B f).symm

/-- The dual all-original-arrow predicate has the same exact inverse-image description. -/
theorem cocartesianRelativeHomotopyTesting_arrow_inverseImage (B : SSet.{u}) [Quasicategory B] :
    (cocartesianRelativeHomotopyTesting B).arrowObjectProperty =
      surjectiveArrows.{u}.inverseImage (cocartesianRelativeWeakLiftingTest B) := by
  funext f
  exact propext (cocartesianRelativeWeakLiftingTest_surjective_iff B f).symm

/-- A genuine common regular accessibility rank is produced for all original Cartesian relative homotopy
  weak arrows and their exact inclusion. -/
theorem cartesianRelativeHomotopyTesting_isAccessible (B : SSet.{u}) [Quasicategory B] :
    MorphismProperty.IsAccessible.{u} (cartesianRelativeHomotopyTesting B) := by
  let _ : IsLocallyPresentable.{u} (Over (max B)) := over_isLocallyPresentable (max B)
  let _ : IsAccessibleCategory.{u} (Over (max B)) := inferInstance
  let _ : IsAccessibleCategory.{u} (Arrow (Over (max B))) := inferInstance
  let _ : IsAccessibleCategory.{u} (Arrow (Type u)) :=
    ⟨Cardinal.aleph0, Cardinal.fact_isRegular_aleph0, inferInstance⟩
  let _ : Functor.IsAccessible.{u} (cartesianRelativeWeakLiftingTest B) :=
    cartesianRelativeWeakLiftingTest_isAccessible B
  obtain ⟨hSurj, hIncl⟩ := surjectiveArrow_accessible.{u}
  let _ : IsAccessibleCategory.{u} SurjectiveArrow.{u} := hSurj
  let _ : Functor.IsAccessible.{u} surjectiveArrows.{u}.ι := hIncl
  obtain ⟨κ, hκ, hC, hI⟩ := inverseImage_accessible (cartesianRelativeWeakLiftingTest B) surjectiveArrows.{u}
  let _ : Fact κ.IsRegular := hκ
  rw [← cartesianRelativeHomotopyTesting_arrow_inverseImage B] at hC hI
  exact ⟨κ, hκ, ⟨hC, hI⟩⟩

/-- The same original-universe construction produces accessibility of every dual relative homotopy weak
  arrow and original square. -/
theorem cocartesianRelativeHomotopyTesting_isAccessible (B : SSet.{u}) [Quasicategory B] :
    MorphismProperty.IsAccessible.{u} (cocartesianRelativeHomotopyTesting B) := by
  let _ : IsLocallyPresentable.{u} (Over (max B)) := over_isLocallyPresentable (max B)
  let _ : IsAccessibleCategory.{u} (Over (max B)) := inferInstance
  let _ : IsAccessibleCategory.{u} (Arrow (Over (max B))) := inferInstance
  let _ : IsAccessibleCategory.{u} (Arrow (Type u)) :=
    ⟨Cardinal.aleph0, Cardinal.fact_isRegular_aleph0, inferInstance⟩
  let _ : Functor.IsAccessible.{u} (cocartesianRelativeWeakLiftingTest B) :=
    cocartesianRelativeWeakLiftingTest_isAccessible B
  obtain ⟨hSurj, hIncl⟩ := surjectiveArrow_accessible.{u}
  let _ : IsAccessibleCategory.{u} SurjectiveArrow.{u} := hSurj
  let _ : Functor.IsAccessible.{u} surjectiveArrows.{u}.ι := hIncl
  obtain ⟨κ, hκ, hC, hI⟩ := inverseImage_accessible (cocartesianRelativeWeakLiftingTest B) surjectiveArrows.{u}
  let _ : Fact κ.IsRegular := hκ
  rw [← cocartesianRelativeHomotopyTesting_arrow_inverseImage B] at hC hI
  exact ⟨κ, hκ, ⟨hC, hI⟩⟩

end SSet.Marked
