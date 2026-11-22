/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaReplacement

/-!
# Strict public use of the chosen omega auxiliary replacement
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits SSet.joyalInterval

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaReplacement

/-- The complete result concerns the original chosen unit and its same target. -/
theorem chosen_replacement (X : SSet.{u}) :
    auxiliaryAnodyneExtensions (auxiliaryOmegaFreeFillerUnit.app X) ∧
      auxiliaryNaiveFibrations (terminal.from (auxiliaryOmegaFreeFiller.obj X)) :=
  auxiliaryOmegaFreeFiller_isReplacement X

/-- Every supplied original labelled-generator square has both strict diagonal equations. -/
theorem generator_square (X : SSet.{u}) (i : AuxiliaryGeneratorIndex.{u})
    (a : (auxiliaryGeneratorArrow i).left ⟶ auxiliaryOmegaFreeFiller.obj X)
    (b : (auxiliaryGeneratorArrow i).right ⟶ ⊤_ SSet.{u})
    (sq : CommSq a (auxiliaryGeneratorArrow i).hom
      (terminal.from (auxiliaryOmegaFreeFiller.obj X)) b) :
    ∃ l : (auxiliaryGeneratorArrow i).right ⟶ auxiliaryOmegaFreeFiller.obj X,
      (auxiliaryGeneratorArrow i).hom ≫ l = a ∧
        l ≫ terminal.from (auxiliaryOmegaFreeFiller.obj X) = b := by
  have hNF := (chosen_replacement X).2
  rw [auxiliaryNaiveFibrations_eq_generatorRlp, auxiliaryGenerators_eq_ofHoms] at hNF
  have hip : HasLiftingProperty (auxiliaryGeneratorArrow i).hom
      (terminal.from (auxiliaryOmegaFreeFiller.obj X)) :=
    hNF _ (MorphismProperty.ofHoms.mk i)
  have : sq.HasLift := hip.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaReplacement
