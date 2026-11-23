/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatRightProper

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe u

namespace TopCat.RightProperTests

-- Merely importing the provider does not opt in to the selected model.
/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
example : ModelCategory TopCat.{u} := by
  infer_instance

open scoped TopCat.modelCategory

-- Opening the model scope still does not install right properness.
/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
example : IsRightProper TopCat.{u} := by
  infer_instance

example : IsRightProper TopCat.{u} :=
  TopCat.modelCategory.rightProper

example {A B X Y : TopCat.{u}}
    {p' : A ⟶ B} {f' : A ⟶ X} {f : B ⟶ Y} {p : X ⟶ Y}
    (sq : IsPullback p' f' f p) [Fibration p] [WeakEquivalence f] :
    WeakEquivalence f' := by
  let _ : IsRightProper TopCat.{u} :=
    TopCat.modelCategory.rightProper
  exact IsRightProper.weakEquivalence_of_isPullback sq

-- The proof-local installation above does not leak.
/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
example : IsRightProper TopCat.{u} := by
  infer_instance

section UniverseOne

example : IsRightProper TopCat.{1} :=
  TopCat.modelCategory.rightProper

end UniverseOne

section UniverseZero

example : IsRightProper TopCat.{0} :=
  TopCat.modelCategory.rightProper

end UniverseZero

#check TopCat.modelCategory.rightProper
#print axioms TopCat.modelCategory.rightProper

end TopCat.RightProperTests
