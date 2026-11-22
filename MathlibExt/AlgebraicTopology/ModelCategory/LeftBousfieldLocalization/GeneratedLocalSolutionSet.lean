/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

-- Author: @toskua, Codex
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.GeneratedLocalArrowAccessibility
import Mathlib.CategoryTheory.Presentable.SolutionSetCondition

/-!
# Solution sets for the actual original derived local-equivalence arrows

The full original arrow class and its original inclusion are first proved
accessible from the original model, action, generation and presentability.
Only then is the existing accessible-functor solution-set theorem applied.
Every original generating cofibration and every incoming commuting square is
retained, with no cofibrancy or fibrancy restriction on solution arrows.
-/

set_option autoImplicit false

noncomputable section

universe w wS u v

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.GeneratedLocalReplacement

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (a : CompatibleSimplicialMapping.Action C)
  {K : Type wS} (S : K → Arrow C) [Small.{w} K]
  [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
  [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]
  (κLP : Cardinal.{w}) [Fact κLP.IsRegular] [IsCardinalLocallyPresentable C κLP]

include d a κLP in
/-- The actual original local-equivalence inclusion satisfies the full solution-set condition. -/
theorem originalLocalEquivalences_solutionSetCondition :
    SolutionSetCondition.{w} (localEquivalences S).arrowObjectProperty.ι := by
  obtain ⟨ν, hν, hW⟩ := originalLocalEquivalences_accessible d a S κLP
  let _ : Fact ν.IsRegular := hν
  let _ : (localEquivalences S).IsCardinalAccessible ν := hW
  let _ : IsAccessibleCategory.{w} (localEquivalences S).arrowObjectProperty.FullSubcategory :=
    ⟨ν, inferInstance, inferInstance⟩
  let _ : Functor.IsAccessible.{w} (localEquivalences S).arrowObjectProperty.ι :=
    Functor.isAccessible_of_isCardinalAccessible _ ν
  let _ : IsAccessibleCategory.{w} C := ⟨κLP, inferInstance, inferInstance⟩
  let _ : IsAccessibleCategory.{w} (Arrow C) := ⟨κLP, inferInstance, inferInstance⟩
  exact SolutionSetCondition.of_isCardinalAccessible (localEquivalences S).arrowObjectProperty.ι

include d a κLP in
/-- A small family factors every original square from any supplied original arrow. -/
theorem originalLocalEquivalences_solutionSets (A : Arrow C) :
    ∃ (ι : Type w) (B : ι → (localEquivalences S).arrowObjectProperty.FullSubcategory)
      (f : ∀ k, A ⟶ (localEquivalences S).arrowObjectProperty.ι.obj (B k)),
      ∀ (Y : (localEquivalences S).arrowObjectProperty.FullSubcategory)
        (h : A ⟶ (localEquivalences S).arrowObjectProperty.ι.obj Y),
        ∃ (k : ι) (g : B k ⟶ Y),
          f k ≫ (localEquivalences S).arrowObjectProperty.ι.map g = h :=
  originalLocalEquivalences_solutionSetCondition d a S κLP A

include a κLP in
/-- Every actual original generating cofibration has a small solution family for all original
commuting squares into all original local-equivalence arrows. -/
theorem originalGeneratingCofibrations_solutionSets (i : d.I.toSet) :
    ∃ (ι : Type w) (B : ι → (localEquivalences S).arrowObjectProperty.FullSubcategory)
      (f : ∀ k, i.1 ⟶ (localEquivalences S).arrowObjectProperty.ι.obj (B k)),
      ∀ (Y : (localEquivalences S).arrowObjectProperty.FullSubcategory)
        (h : i.1 ⟶ (localEquivalences S).arrowObjectProperty.ι.obj Y),
        ∃ (k : ι) (g : B k ⟶ Y),
          f k ≫ (localEquivalences S).arrowObjectProperty.ι.map g = h :=
  originalLocalEquivalences_solutionSets d a S κLP i.1

include a κLP in
/-- Original combinatorial simplicial source data produces regular full-arrow accessibility
and the complete original generatorwise solution sets. -/
theorem originalLocalEquivalences_accessibility_and_solutionSets :
    ∃ (ν : Cardinal.{w}) (_ : Fact ν.IsRegular),
      (localEquivalences S).IsCardinalAccessible ν ∧
        ∀ i : d.I.toSet,
          ∃ (ι : Type w) (B : ι → (localEquivalences S).arrowObjectProperty.FullSubcategory)
            (f : ∀ k, i.1 ⟶ (localEquivalences S).arrowObjectProperty.ι.obj (B k)),
            ∀ (Y : (localEquivalences S).arrowObjectProperty.FullSubcategory)
              (h : i.1 ⟶ (localEquivalences S).arrowObjectProperty.ι.obj Y),
              ∃ (k : ι) (g : B k ⟶ Y),
                f k ≫ (localEquivalences S).arrowObjectProperty.ι.map g = h := by
  obtain ⟨ν, hν, hW⟩ := originalLocalEquivalences_accessible d a S κLP
  exact ⟨ν, hν, hW, originalGeneratingCofibrations_solutionSets d a S κLP⟩

end HomotopicalAlgebra.GeneratedLocalReplacement
