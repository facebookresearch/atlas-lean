/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.AlgebraicTopology.ModelCategory.Proper

/-!
# Proper model category tests

These tests pin the weakest parent assumptions, pushout and pullback leg
orientations, all-object criteria, wrapper-instance boundary, and absence of
automatic opposite properness.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty

universe v u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.ProperTests

open HomotopicalAlgebra

section WeakestLeftParents

variable {C : Type u} [Category.{v} C]
  [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C]

example [IsLeftProper C] :
    (weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C) := by
  infer_instance

example [IsLeftProper C]
    {A B X Y : C}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) [Cofibration i] [WeakEquivalence f] :
    WeakEquivalence f' :=
  IsLeftProper.weakEquivalence_of_isPushout sq

example : Unit := by
  fail_if_success let _ : IsLeftProper C := inferInstance
  exact ()

end WeakestLeftParents

section WeakestRightParents

variable {C : Type u} [Category.{v} C]
  [CategoryWithWeakEquivalences C] [CategoryWithFibrations C]

example [IsRightProper C] :
    (weakEquivalences C).IsStableUnderBaseChangeAgainst (fibrations C) := by
  infer_instance

example [IsRightProper C]
    {A B X Y : C}
    {p' : A ⟶ B} {f' : A ⟶ X} {f : B ⟶ Y} {p : X ⟶ Y}
    (sq : IsPullback p' f' f p) [Fibration p] [WeakEquivalence f] :
    WeakEquivalence f' :=
  IsRightProper.weakEquivalence_of_isPullback sq

example : Unit := by
  fail_if_success let _ : IsRightProper C := inferInstance
  exact ()

end WeakestRightParents

section ModelCategoryCriteria

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- A bare model category does not acquire the left wrapper automatically;
the all-cofibrant criterion remains an ordinary theorem. -/
example (h : ∀ X : C, IsCofibrant X) : IsLeftProper C := by
  fail_if_success infer_instance
  exact isLeftProper_of_all_objects_cofibrant h

/-- The right criterion is likewise explicit rather than an instance. -/
example (h : ∀ X : C, IsFibrant X) : IsRightProper C := by
  fail_if_success infer_instance
  exact isRightProper_of_all_objects_fibrant h

example [IsLeftProper C] {A B : C} (i : A ⟶ B) [Cofibration i] :
    WeakEquivalence (𝟙 B) := by
  exact IsLeftProper.weakEquivalence_of_isPushout
    (IsPushout.of_id_snd (f := i))

example [IsLeftProper C] {A X : C} (f : A ⟶ X) [WeakEquivalence f] :
    WeakEquivalence f := by
  exact IsLeftProper.weakEquivalence_of_isPushout
    (IsPushout.of_id_fst (f := f))

example [IsRightProper C] {X Y : C} (p : X ⟶ Y) [Fibration p] :
    WeakEquivalence (𝟙 X) := by
  exact IsRightProper.weakEquivalence_of_isPullback
    (IsPullback.of_id_snd (f := p))

example [IsRightProper C] {B Y : C} (f : B ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence f := by
  exact IsRightProper.weakEquivalence_of_isPullback
    (IsPullback.of_id_fst (f := f))

/-- Installing left properness does not install the mathematically dual
opposite wrapper as an automatic instance. -/
example [IsLeftProper C] : Unit := by
  fail_if_success let _ : IsRightProper Cᵒᵖ := inferInstance
  exact ()

/-- Installing right properness likewise creates no automatic opposite
wrapper. -/
example [IsRightProper C] : Unit := by
  fail_if_success let _ : IsLeftProper Cᵒᵖ := inferInstance
  exact ()

end ModelCategoryCriteria

#check HomotopicalAlgebra.IsLeftProper
#check HomotopicalAlgebra.IsRightProper
#check HomotopicalAlgebra.IsLeftProper.weakEquivalence_of_isPushout
#check HomotopicalAlgebra.IsRightProper.weakEquivalence_of_isPullback
#check HomotopicalAlgebra.isLeftProper_of_all_objects_cofibrant
#check HomotopicalAlgebra.isRightProper_of_all_objects_fibrant

#print axioms HomotopicalAlgebra.IsLeftProper.weakEquivalence_of_isPushout
#print axioms HomotopicalAlgebra.IsRightProper.weakEquivalence_of_isPullback
#print axioms HomotopicalAlgebra.isLeftProper_of_all_objects_cofibrant
#print axioms HomotopicalAlgebra.isRightProper_of_all_objects_fibrant

end MathlibExtTest.AlgebraicTopology.ModelCategory.ProperTests
