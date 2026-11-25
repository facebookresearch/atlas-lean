/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.NaiveFibrations

/-!
# Public use of naive fibrations for an explicit class

Consumers obtain actual extensions into naive fibrant objects and solve
fully prescribed squares against naive fibrations. Any terminal object
can be used to test the same object predicate.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe v u

namespace NaiveFibrationsTest

variable {C : Type u} [Category.{v} C]
variable (An : MorphismProperty C) {A B X Y T : C}

/-- Choose an actual extension with its strict restriction equation. -/
noncomputable def chosenExtension [HasTerminal C] (hX : An.naiveFibrantObjects X)
    (i : A ⟶ B) (hi : An i) (f : A ⟶ X) :
    {g : B ⟶ X // i ≫ g = f} :=
  let h := (An.naiveFibrantObjects_iff_extensions X).1 hX i hi f
  ⟨h.choose, h.choose_spec⟩

/-- The right lifting class solves the full supplied square over any base. -/
lemma prescribed_square {i : A ⟶ B} {p : X ⟶ Y} (hi : An i)
    (hp : An.naiveFibrations p) {a : A ⟶ X} {b : B ⟶ Y}
    (sq : CommSq a i p b) :
    ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b := by
  have hip : HasLiftingProperty i p := hp i hi
  have : sq.HasLift := hip.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- The object predicate transfers to an actual map to an arbitrary terminal. -/
lemma map_to_terminal [HasTerminal C] (hX : An.naiveFibrantObjects X)
    (p : X ⟶ T) (hT : IsTerminal T) : An.naiveFibrations p :=
  (An.naiveFibrantObjects_iff_of_isTerminal p hT).1 hX

end NaiveFibrationsTest
