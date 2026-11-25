/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.TrivialCofibrationStrongDeformation

/-!
# Tests for the generic trivial-cofibration deformation constructor
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.Precylinder.TrivialCofibrationStrongDeformationTest

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (P : Precylinder (𝟭 C)) {X Y : C} (i : X ⟶ Y)

/-- The constructor retains the strict retraction, both endpoint equations, and
full stationarity on the original source cylinder. -/
theorem all_equations
    (hi : trivialCofibrations C i)
    (hcorner : trivialCofibrations C (P.boundaryCorner i))
    (hX : IsFibrant X) (hY : IsFibrant Y) :
    ∃ D : P.StrongDeformationData i,
      i ≫ D.retraction = 𝟙 X ∧
        (P.app Y).i₀ ≫ D.homotopy.h = 𝟙 Y ∧
        (P.app Y).i₁ ≫ D.homotopy.h = D.retraction ≫ i ∧
        P.I.map i ≫ D.homotopy.h = (P.app X).π ≫ i := by
  obtain ⟨D⟩ :=
    P.nonempty_strongDeformationData_of_trivialCofibration
      i hi hcorner hX hY
  exact ⟨D, D.retract, D.homotopy.h₀, D.homotopy.h₁, D.stationary⟩

end HomotopicalAlgebra.Precylinder.TrivialCofibrationStrongDeformationTest
