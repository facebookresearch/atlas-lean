/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkModelCategory

/-!
# Rezk fibrations are vertical Reedy fibrations

The actual Rezk model is a left localization of the named vertical Reedy
model: both cofibration classes are the monomorphisms and every Reedy weak
equivalence is Rezk weak. Consequently every Rezk fibration has the right
lifting property against every Reedy trivial cofibration.

This gives a global one-way inclusion of fibration classes. The source-facing
corollaries retain complete Segal source and target hypotheses and expose the
original relative matching maps. No converse or equality of the two global
fibration classes is asserted.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory HomotopicalAlgebra
open CategoryTheory.MorphismProperty

namespace SimplicialSpace.RezkModel

/-- Every fibration in the actual Rezk model is a fibration in the vertical
Reedy model. -/
theorem fibrations_le_reedyFibrations :
    modelCategory.{u}.categoryWithFibrations.fibrations ≤
      ReedyModel.modelCategory.{u}.categoryWithFibrations.fibrations := by
  rw [modelCategory_fibrations]
  intro X Y f hf
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  change fibrations SimplicialSpace.{u} f
  rw [← trivialCofibrations_rlp]
  intro A B i hi
  apply hf i
  have hiCof : Cofibration i := ⟨hi.1⟩
  exact ⟨(ReedyModel.cofibration_iff i).1 hiCof,
    reedyWeak_le_rezkWeak i hi.2⟩

/-- A concrete Rezk fibration is a vertical Reedy fibration, without endpoint
restrictions. -/
theorem reedyFibration_of_fibration {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y)
    (hf : modelCategory.{u}.categoryWithFibrations.fibrations f) :
    ReedyModel.modelCategory.{u}.categoryWithFibrations.fibrations f :=
  fibrations_le_reedyFibrations f hf

/-- Source-facing endpoint-restricted form: a Rezk fibration between complete
Segal spaces is a vertical Reedy fibration. The endpoint hypotheses are kept
because this is the exact formulation stated after Joyal--Tierney Theorem 4.1,
even though the constructed class inclusion proves this direction globally. -/
theorem reedyFibration_of_fibration_of_completeSegalSpaces
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (hX : completeSegalSpaces X) (hY : completeSegalSpaces Y)
    (hf : modelCategory.{u}.categoryWithFibrations.fibrations f) :
    ReedyModel.modelCategory.{u}.categoryWithFibrations.fibrations f := by
  rcases hX with ⟨_, _⟩
  rcases hY with ⟨_, _⟩
  exact reedyFibration_of_fibration f hf

/-- Every original vertical relative matching map of a Rezk fibration between
complete Segal spaces is a Kan fibration. -/
theorem relativeMatchingMap_mem_of_fibration_of_completeSegalSpaces
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (hX : completeSegalSpaces X) (hY : completeSegalSpaces Y)
    (hf : modelCategory.{u}.categoryWithFibrations.fibrations f) :
    ∀ n : ℕ, SSet.modelCategoryQuillen.J.{u}.rlp
      (SimplicialObject.relativeMatchingMap
        (SimplicialSpace.forget.map f) n) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  apply (ReedyModel.fibration_iff f).1
  apply (HomotopicalAlgebra.fibration_iff f).2
  exact reedyFibration_of_fibration_of_completeSegalSpaces f hX hY hf

end SimplicialSpace.RezkModel
