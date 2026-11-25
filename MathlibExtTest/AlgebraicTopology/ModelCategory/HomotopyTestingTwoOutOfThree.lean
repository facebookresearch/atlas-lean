/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingTwoOutOfThree

/-!
# Public use of testing two-out-of-three

All three native morphism-property directions require only the actual
testing memberships. Cancellation also supplies an actual preimage on
the homotopy classes of a specified naive fibrant target.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe v u

namespace HomotopyTestingTwoOutOfThreeTest

variable {C : Type u} [Category.{v} C] (P : Precylinder (𝟭 C))
  (An : MorphismProperty C) [HasTerminal C] {X Y Z T : C}

/-- Native composition closes the testing class. -/
lemma comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : P.testingEquivalences An f) (hg : P.testingEquivalences An g) :
    P.testingEquivalences An (f ≫ g) :=
  (P.testingEquivalences An).comp_mem f g hf hg

/-- Cancel a testing first map from a testing composite. -/
lemma cancel_first (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : P.testingEquivalences An f) (hfg : P.testingEquivalences An (f ≫ g)) :
    P.testingEquivalences An g :=
  (P.testingEquivalences An).of_precomp f g hf hfg

/-- Cancel a testing second map from a testing composite. -/
lemma cancel_second (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : P.testingEquivalences An g) (hfg : P.testingEquivalences An (f ≫ g)) :
    P.testingEquivalences An f :=
  (P.testingEquivalences An).of_postcomp f g hg hfg

/-- Cancellation yields a preimage for the actual contravariant class map. -/
lemma exists_class_preimage_after_cancel_first (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : P.testingEquivalences An f) (hfg : P.testingEquivalences An (f ≫ g))
    (hT : An.naiveFibrantObjects T) (α : P.HomotopyClass Y T) :
    ∃ β : P.HomotopyClass Z T, P.homotopyClassPrecomp g T β = α :=
  ((P.testingEquivalences An).of_precomp f g hf hfg T hT).surjective α

end HomotopyTestingTwoOutOfThreeTest
