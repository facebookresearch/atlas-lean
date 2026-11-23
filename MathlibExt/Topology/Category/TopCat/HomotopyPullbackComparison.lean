/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatStrictFiberHomotopyFiber

/-!
# The stock constant-path comparison of a strict square

The original compact-open homotopy pullback receives the two original maps
and the constant path at their common base image. The constructor and its
three coordinate proofs are moved unchanged from
`HomotopyCartesianOpenCoverDescent`; the original names are preserved.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopCat

/-- The actual constant-path comparison of a strict commutative square. -/
def homotopyPullbackComparison
    {A E W B : TopCat.{u}} {s : A ⟶ E} {q : A ⟶ W}
    {p : E ⟶ B} {h : W ⟶ B} (sq : CommSq s q p h) :
    A ⟶ homotopyPullback p h :=
  pullback.lift (prod.lift s q) (s ≫ p ≫ pathConstant B) (by
    apply prod.hom_ext
    · simp [pathEndpoints]
    · simpa [pathEndpoints] using sq.w.symm)

/-- The comparison retains the given total-space map. -/
@[reassoc (attr := simp)]
theorem homotopyPullbackComparison_left
    {A E W B : TopCat.{u}} {s : A ⟶ E} {q : A ⟶ W}
    {p : E ⟶ B} {h : W ⟶ B} (sq : CommSq s q p h) :
    homotopyPullbackComparison sq ≫ homotopyPullbackLeft p h = s := by
  rw [homotopyPullbackComparison, ← Category.assoc, pullback.lift_fst]
  simp

/-- The comparison retains the given restriction projection. -/
@[reassoc (attr := simp)]
theorem homotopyPullbackComparison_right
    {A E W B : TopCat.{u}} {s : A ⟶ E} {q : A ⟶ W}
    {p : E ⟶ B} {h : W ⟶ B} (sq : CommSq s q p h) :
    homotopyPullbackComparison sq ≫ homotopyPullbackRight p h = q := by
  rw [homotopyPullbackComparison, ← Category.assoc, pullback.lift_fst]
  simp

/-- The comparison's path is constant at the common base coordinate. -/
@[reassoc (attr := simp)]
theorem homotopyPullbackComparison_path
    {A E W B : TopCat.{u}} {s : A ⟶ E} {q : A ⟶ W}
    {p : E ⟶ B} {h : W ⟶ B} (sq : CommSq s q p h) :
    homotopyPullbackComparison sq ≫ homotopyPullbackPath p h =
      s ≫ p ≫ pathConstant B := by
  rw [homotopyPullbackComparison, pullback.lift_snd]


end TopCat

end
