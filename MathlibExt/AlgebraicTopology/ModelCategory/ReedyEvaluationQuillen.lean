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

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ReedyGenerated
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction
public import Mathlib.CategoryTheory.Adjunction.Evaluation

/-!
# Evaluation on the actual source Reedy model

The original latching and matching component lemmas prove all four
evaluation preservation classes. The actual stock evaluation adjunctions
are then Quillen for the model constructed from the caller's original
coefficient factorization data. No diagram model or Quillen outcome is
supplied as an input.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uJ vJ uD uC vC w

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.ReedyModel

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D]
  (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

/-- Every evaluation retains all four source classes of the constructed Reedy model. -/
theorem evaluation_preserves_classes (j : J) :
    letI := modelCategory r Fc Ff
    PreservesCofibrations ((evaluation J C).obj j) ∧
      PreservesTrivialCofibrations ((evaluation J C).obj j) ∧
      PreservesFibrations ((evaluation J C).obj j) ∧
      PreservesTrivialFibrations ((evaluation J C).obj j) := by
  let := modelCategory r Fc Ff
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y f hf
    change ∀ k : J, cofibrations C (CategoryTheory.ReedyStructure.latchingCorner r f k) at hf
    change cofibrations C (f.app j)
    exact component_cofibration_of_latchingCorners r f hf j
  · intro X Y f hf
    rw [trivialCofibrations_eq r Fc Ff] at hf
    change ∀ k : J, trivialCofibrations C (CategoryTheory.ReedyStructure.latchingCorner r f k) at hf
    change trivialCofibrations C (f.app j)
    exact component_trivialCofibration_of_latchingCorners r f hf j
  · intro X Y f hf
    change ∀ k : J, fibrations C (CategoryTheory.ReedyStructure.matchingCorner r f k) at hf
    change fibrations C (f.app j)
    exact component_fibration_of_matchingCorners r f hf j
  · intro X Y f hf
    rw [trivialFibrations_eq r Fc Ff] at hf
    change ∀ k : J, trivialFibrations C (CategoryTheory.ReedyStructure.matchingCorner r f k) at hf
    change trivialFibrations C (f.app j)
    exact component_trivialFibration_of_matchingCorners r f hf j

/-- The stock evaluation/cofree-diagram adjunction is Quillen on the same actual Reedy model. -/
theorem evaluationAdjunctionLeft_isQuillen
    [∀ a b : J, HasProductsOfShape (a ⟶ b) C] (j : J) :
    letI := modelCategory r Fc Ff
    (evaluationAdjunctionLeft C j).IsQuillenAdjunction := by
  let := modelCategory r Fc Ff
  have h := evaluation_preserves_classes r Fc Ff j
  exact ⟨h.1, h.2.1⟩

/-- The stock free-diagram/evaluation adjunction is Quillen on the same actual Reedy model. -/
theorem evaluationAdjunctionRight_isQuillen
    [∀ a b : J, HasCoproductsOfShape (a ⟶ b) C] (j : J) :
    letI := modelCategory r Fc Ff
    (evaluationAdjunctionRight C j).IsQuillenAdjunction := by
  let := modelCategory r Fc Ff
  have h := evaluation_preserves_classes r Fc Ff j
  exact Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations h.2.2.1 h.2.2.2

section GeneratedSource

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

/-- The same evaluation adjunction is Quillen for the original fixed-rank generated Reedy model. -/
theorem generatedEvaluationAdjunctionLeft_isQuillen
    [∀ a b : J, HasProductsOfShape (a ⟶ b) C] (j : J) :
    letI := generatedModelCategory r d
    (evaluationAdjunctionLeft C j).IsQuillenAdjunction :=
  evaluationAdjunctionLeft_isQuillen r d.cofibrantFactorizationData d.fibrantFactorizationData j

/-- The free/evaluation adjunction uses the unchanged original generated coefficient factors. -/
theorem generatedEvaluationAdjunctionRight_isQuillen
    [∀ a b : J, HasCoproductsOfShape (a ⟶ b) C] (j : J) :
    letI := generatedModelCategory r d
    (evaluationAdjunctionRight C j).IsQuillenAdjunction :=
  evaluationAdjunctionRight_isQuillen r d.cofibrantFactorizationData d.fibrantFactorizationData j

end GeneratedSource

end HomotopicalAlgebra.ReedyModel
