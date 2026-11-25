/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.LiftingAfterWeakEquivalence

/-!
# Public consumers of lifting after a weak equivalence

The two transport clients use the general equivalence with no cofibration
assumption on the primed map. The third obtains a primed lift through the
model-category lifting instances and then transports it.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory HomotopicalAlgebra

namespace MathlibExtTest.HomotopicalAlgebra.LiftingAfterWeakEquivalence

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- Restrict a supplied lift to the primed problem using the public forward implication. -/
theorem toPrimed
    {A B B' X Y : C} (a : A ⟶ B) [Cofibration a] (a' : A ⟶ B')
    (f : A ⟶ X) (w : B' ⟶ B) [WeakEquivalence w]
    (r : X ⟶ Y) [Fibration r] (q : B ⟶ Y) (hcomm : a' ≫ w = a)
    (h : ∃ l : B ⟶ X, a ≫ l = f ∧ l ≫ r = q) :
    ∃ l' : B' ⟶ X, a' ≫ l' = f ∧ l' ≫ r = w ≫ q :=
  (exists_lift_iff_of_weakEquivalence a a' f w r q hcomm).mp h

/-- Transport a supplied primed lift using the public reverse implication. -/
theorem fromPrimed
    {A B B' X Y : C} (a : A ⟶ B) [Cofibration a] (a' : A ⟶ B')
    (f : A ⟶ X) (w : B' ⟶ B) [WeakEquivalence w]
    (r : X ⟶ Y) [Fibration r] (q : B ⟶ Y) (hcomm : a' ≫ w = a)
    (h : ∃ l' : B' ⟶ X, a' ≫ l' = f ∧ l' ≫ r = w ≫ q) :
    ∃ l : B ⟶ X, a ≫ l = f ∧ l ≫ r = q :=
  (exists_lift_iff_of_weakEquivalence a a' f w r q hcomm).mpr h

/-- Solve a primed trivial-cofibration square by inference, then transport its diagonal. -/
theorem fromPrimedTrivialCofibration
    {A B B' X Y : C} (a : A ⟶ B) [Cofibration a]
    (a' : A ⟶ B') [Cofibration a'] [WeakEquivalence a']
    (f : A ⟶ X) (w : B' ⟶ B) [WeakEquivalence w]
    (r : X ⟶ Y) [Fibration r] (q : B ⟶ Y) (hcomm : a' ≫ w = a)
    (sq : CommSq f a' r (w ≫ q)) :
    ∃ l : B ⟶ X, a ≫ l = f ∧ l ≫ r = q := by
  let _ : sq.HasLift := inferInstance
  exact (exists_lift_iff_of_weakEquivalence a a' f w r q hcomm).mpr
    ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end MathlibExtTest.HomotopicalAlgebra.LiftingAfterWeakEquivalence
