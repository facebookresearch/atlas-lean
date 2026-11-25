/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.ModelCategory.CylinderHomotopyYoneda

/-!
# Public use of the four homotopy-class criteria

Consumers extract an actual original inverse with its two generated-class
equations, recover equivalence from either all-object class action, and
obtain testing membership without a model-category assumption.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CylinderHomotopyYonedaTest

variable {C : Type u} [Category.{v} C] (P : HomotopicalAlgebra.Precylinder (𝟭 C))
variable {X Y : C} (f : X ⟶ Y)

/-- The common criterion returns an original map, not merely an inverse class. -/
lemma original_inverse (hf : IsIso (P.homotopyQuotientFunctor.map f)) :
    ∃ g : Y ⟶ X, P.homotopyRel (f ≫ g) (𝟙 X) ∧
      P.homotopyRel (g ≫ f) (𝟙 Y) :=
  (P.homotopyEquivalences_criterion f).1.1 hf

/-- Every-object precomposition testing recovers invertibility of the quotient map. -/
lemma quotient_isIso_of_precomp
    (h : ∀ T : C, Function.Bijective (P.homotopyClassPrecomp f T)) :
    IsIso (P.homotopyQuotientFunctor.map f) :=
  (P.homotopyEquivalences_criterion f).2.2.2 h

/-- Every-object postcomposition testing also gives an actual generated-class inverse. -/
lemma original_inverse_of_postcomp
    (h : ∀ T : C, Function.Bijective
      (fun a : P.HomotopyClass T X ↦ a ≫ P.homotopyQuotientFunctor.map f)) :
    ∃ g : Y ⟶ X, P.homotopyRel (f ≫ g) (𝟙 X) ∧
      P.homotopyRel (g ≫ f) (𝟙 Y) :=
  (P.homotopyEquivalences_criterion f).1.1
    ((P.homotopyEquivalences_criterion f).2.1.2 h)

/-- A pair of generated inverse equations supplies testing membership for any An. -/
lemma testing_of_inverse (An : MorphismProperty C) [HasTerminal C] (g : Y ⟶ X)
    (hfg : P.homotopyRel (f ≫ g) (𝟙 X)) (hgf : P.homotopyRel (g ≫ f) (𝟙 Y)) :
    P.testingEquivalences An f :=
  P.homotopyEquivalences_le_testingEquivalences An f
    ((P.homotopyEquivalences_iff_exists_inverse f).2 ⟨g, hfg, hgf⟩)

end CylinderHomotopyYonedaTest
