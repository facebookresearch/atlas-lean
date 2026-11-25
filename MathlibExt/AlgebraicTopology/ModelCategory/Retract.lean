/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.Retract

/-!
# Retract stability for (co)fibrant objects

For a category with an initial object whose cofibrations are stable under
retracts, a retract of a cofibrant object is cofibrant. The proof exhibits
`initial.to X` as a retract of `initial.to Y` in the arrow category and
applies `MorphismProperty.IsStableUnderRetracts`. The fibrant case is dual
via `terminal.from`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

section Cofibrant

variable [CategoryWithCofibrations C] [HasInitial C]
  [(cofibrations C).IsStableUnderRetracts]

/-- An object retract of a cofibrant object is cofibrant.

The map `initial.to X : ⊥_ C ⟶ X` is a retract of `initial.to Y : ⊥_ C ⟶ Y`
in the arrow category via the retract `X ◁ Y` and the unique maps out of
`⊥_ C`. Stability of cofibrations under retracts then gives the result. -/
theorem isCofibrant_of_retract {X Y : C} (h : Retract X Y) [IsCofibrant Y] :
    IsCofibrant X := by
  have hY : cofibrations C (initial.to Y) := (cofibration_iff (f := initial.to Y)).mp inferInstance
  have hRetract : RetractArrow (initial.to X) (initial.to Y) :=
    { i := Arrow.homMk (𝟙 (⊥_ C)) h.i (by simp)
      r := Arrow.homMk (𝟙 (⊥_ C)) h.r (by simp)
      retract := by
        ext
        · simp
        · simp [h.retract] }
  have hX : cofibrations C (initial.to X) := MorphismProperty.of_retract hRetract hY
  exact (cofibration_iff (f := initial.to X)).mpr hX

end Cofibrant

section Fibrant

variable [CategoryWithFibrations C] [HasTerminal C]
  [(fibrations C).IsStableUnderRetracts]

/-- An object retract of a fibrant object is fibrant.

Dual to `isCofibrant_of_retract`: `terminal.from X : X ⟶ ⊤_ C` is a retract
of `terminal.from Y` via the given object retract and the unique maps into
`⊤_ C`, and fibrations are stable under retracts. -/
theorem isFibrant_of_retract {X Y : C} (h : Retract X Y) [IsFibrant Y] :
    IsFibrant X := by
  have hY : fibrations C (terminal.from Y) :=
    (fibration_iff (f := terminal.from Y)).mp inferInstance
  have hRetract : RetractArrow (terminal.from X) (terminal.from Y) :=
    { i := Arrow.homMk h.i (𝟙 (⊤_ C)) (by simp)
      r := Arrow.homMk h.r (𝟙 (⊤_ C)) (by simp)
      retract := by
        ext
        · simp [h.retract]
        · simp }
  have hX : fibrations C (terminal.from X) := MorphismProperty.of_retract hRetract hY
  exact (fibration_iff (f := terminal.from X)).mpr hX

end Fibrant

end HomotopicalAlgebra
