/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.EvaluationTransfer
public import MathlibExt.AlgebraicTopology.ModelCategory.Proper
public import MathlibExt.CategoryTheory.MorphismProperty.Limits

/-!
# Properness through original evaluation functors

Only the actual weak/cofibration dictionaries and preserved original pushout
squares are used. The base cobase predicate may be against a separate class.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe s uC vC uM vM

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.EvaluationTransfer

variable {C : Type uC} [Category.{vC} C]
  {M : Type uM} [Category.{vM} M] {S : Type s}

/-- An original family of preserved pushouts transfers base cobase stability. -/
theorem cobaseChangeAgainst_of_evaluations
    (R : S → C ⥤ M) (W P : MorphismProperty C) (WM Q : MorphismProperty M)
    (hW : W = evaluationProperty R WM)
    (hP : P ≤ evaluationProperty R Q)
    (hBase : WM.IsStableUnderCobaseChangeAgainst Q)
    (hPush : ∀ (s : S) {A B X : C} (i : A ⟶ B) (f : A ⟶ X),
      P i → W f → PreservesColimit (span i f) (R s)) :
    W.IsStableUnderCobaseChangeAgainst P := by
  constructor
  intro A B i hi
  constructor
  intro X Y j f' f sq hf
  rw [hW]
  apply (evaluationProperty_iff R WM f').2
  intro s
  let : PreservesColimit (span i f) (R s) := hPush s i f hi hf
  have hiImage : Q ((R s).map i) :=
    (evaluationProperty_iff R Q i).1 (hP i hi) s
  have hfImage : ∀ t : S, WM ((R t).map f) := by
    apply (evaluationProperty_iff R WM f).1
    rw [← hW]
    exact hf
  exact hBase.of_isPushout (sq.map (R s)) hiImage (hfImage s)

/-- Prove properness of the same original weak/cofibration dictionaries. -/
theorem isLeftProper_of_evaluations
    [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C]
    [CategoryWithWeakEquivalences M]
    (R : S → C ⥤ M) (Q : MorphismProperty M)
    (hW : weakEquivalences C = evaluationProperty R (weakEquivalences M))
    (hCof : cofibrations C ≤ evaluationProperty R Q)
    (hBase : (weakEquivalences M).IsStableUnderCobaseChangeAgainst Q)
    (hPush : ∀ (s : S) {A B X : C} (i : A ⟶ B) (f : A ⟶ X),
      cofibrations C i → weakEquivalences C f →
        PreservesColimit (span i f) (R s)) :
    IsLeftProper C where
  weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations :=
    cobaseChangeAgainst_of_evaluations R (weakEquivalences C)
      (cofibrations C) (weakEquivalences M) Q hW hCof hBase hPush

end HomotopicalAlgebra.EvaluationTransfer
