/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingRetracts

/-!
# Public use of testing-equivalence retract closure

The native closure API consumes an actual arrow retract. Component data
can construct that retract, and class precomposition transports it through
the opposite category with its correct reversal.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomotopyTestingRetractsTest

variable {C : Type u} [Category.{v} C] (P : HomotopicalAlgebra.Precylinder (𝟭 C))
variable {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W}

/-- Instance inference supplies the native per-map retract closure API. -/
lemma of_retract (An : MorphismProperty C) [HasTerminal C]
    (h : RetractArrow f g) (hg : P.testingEquivalences An g) :
    P.testingEquivalences An f :=
  MorphismProperty.of_retract h hg

/-- Contravariant class precomposition retains an actual arrow retract for every target. -/
def classRetract (T : C) (h : RetractArrow f g) :
    RetractArrow ((P.homotopyClassFunctor T).map f.op)
      ((P.homotopyClassFunctor T).map g.op) :=
  h.op.map (P.homotopyClassFunctor T)

/-- Fully prescribed component retraction data give testing membership. -/
lemma of_component_retraction (An : MorphismProperty C) [HasTerminal C]
    (iX : X ⟶ Z) (iY : Y ⟶ W) (rX : Z ⟶ X) (rY : W ⟶ Y)
    (hi : iX ≫ g = f ≫ iY) (hr : rX ≫ f = g ≫ rY)
    (hX : iX ≫ rX = 𝟙 X) (hY : iY ≫ rY = 𝟙 Y)
    (hg : P.testingEquivalences An g) : P.testingEquivalences An f := by
  let h : RetractArrow f g :=
    { i := Arrow.homMk iX iY hi
      r := Arrow.homMk rX rY hr
      retract := by
        ext
        · exact hX
        · exact hY }
  exact MorphismProperty.of_retract h hg

end HomotopyTestingRetractsTest
