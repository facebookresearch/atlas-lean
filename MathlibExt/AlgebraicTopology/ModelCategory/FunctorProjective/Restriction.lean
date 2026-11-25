/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Data
import MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory.Restriction

/-!
# Actual restriction between original projective models

Precomposition is the native `Functor.whiskeringLeft`. The fixed-data
entry retains both independently supplied original data and cardinals.
-/

set_option autoImplicit false
noncomputable section
universe uD vD uE vE uM vM wD wE
open CategoryTheory Functor MorphismProperty

namespace HomotopicalAlgebra.FunctorProjective.Restriction

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {M : Type uM} [Category.{vM} M] [ModelCategory M]

/-- The actual prescribed pointwise weak classes are preserved by original restriction. -/
theorem preserves_weakEquivalences_of_eqs
    [CategoryWithWeakEquivalences (D ⥤ M)] [CategoryWithWeakEquivalences (E ⥤ M)]
    (hWD : weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D)
    (hWE : weakEquivalences (E ⥤ M) = (weakEquivalences M).functorCategory E)
    (u : D ⥤ E) :
    weakEquivalences (E ⥤ M) ≤
      (weakEquivalences (D ⥤ M)).inverseImage ((whiskeringLeft D E M).obj u) := by
  rw [hWE, hWD]
  exact functorCategory_le_inverseImage_whiskeringLeft (weakEquivalences M) u

/-- Original restriction preserves both actual prescribed projective right classes. -/
theorem preserves_right_classes_of_eqs
    [CategoryWithFibrations (D ⥤ M)] [CategoryWithFibrations (E ⥤ M)]
    [CategoryWithWeakEquivalences (D ⥤ M)] [CategoryWithWeakEquivalences (E ⥤ M)]
    (hFD : fibrations (D ⥤ M) = (fibrations M).functorCategory D)
    (hFE : fibrations (E ⥤ M) = (fibrations M).functorCategory E)
    (hTD : trivialFibrations (D ⥤ M) = (trivialFibrations M).functorCategory D)
    (hTE : trivialFibrations (E ⥤ M) = (trivialFibrations M).functorCategory E)
    (u : D ⥤ E) :
    PreservesFibrations ((whiskeringLeft D E M).obj u) ∧
      PreservesTrivialFibrations ((whiskeringLeft D E M).obj u) := by
  constructor
  · change fibrations (E ⥤ M) ≤
      (fibrations (D ⥤ M)).inverseImage ((whiskeringLeft D E M).obj u)
    rw [hFE, hFD]
    exact functorCategory_le_inverseImage_whiskeringLeft (fibrations M) u
  · change trivialFibrations (E ⥤ M) ≤
      (trivialFibrations (D ⥤ M)).inverseImage ((whiskeringLeft D E M).obj u)
    rw [hTE, hTD]
    exact functorCategory_le_inverseImage_whiskeringLeft (trivialFibrations M) u

variable {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  {κE : Cardinal.{wE}} [Fact κE.IsRegular] [OrderBot κE.ord.ToType]
  [Small.{wD} D] [LocallySmall.{wD} D] [Small.{wE} E] [LocallySmall.{wE} E]

/-- The two independently supplied data retain their exact original projective models. -/
theorem preserves_classes (dD : CofibrantGenerationData M κD)
    (dE : CofibrantGenerationData M κE) (u : D ⥤ E) :
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    (weakEquivalences (E ⥤ M) ≤
      (weakEquivalences (D ⥤ M)).inverseImage ((whiskeringLeft D E M).obj u)) ∧
      PreservesFibrations ((whiskeringLeft D E M).obj u) ∧
        PreservesTrivialFibrations ((whiskeringLeft D E M).obj u) := by
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  exact ⟨preserves_weakEquivalences_of_eqs
    (FunctorProjective.weakEquivalences_eq.{wD} dD)
    (FunctorProjective.weakEquivalences_eq.{wE} dE) u,
    preserves_right_classes_of_eqs (FunctorProjective.fibrations_eq.{wD} dD)
      (FunctorProjective.fibrations_eq.{wE} dE)
      (FunctorProjective.trivialFibrations_eq.{wD} dD)
      (FunctorProjective.trivialFibrations_eq.{wE} dE) u⟩

end HomotopicalAlgebra.FunctorProjective.Restriction
