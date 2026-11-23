/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyPullbackComparison

/-!
# Clients of the stock comparison without an open-cover import

The original arbitrary square retains both entire maps, its whole constant
target path and both actual endpoint formulas through the focused provider.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace MathlibExtTest.Topology.Category.TopCat.HomotopyPullbackComparisonTests

variable {A E W B : _root_.TopCat.{u}} {s : A ⟶ E} {q : A ⟶ W}
  {p : E ⟶ B} {h : W ⟶ B} (sq : CommSq s q p h)

/-- The original whole left map survives the focused provider boundary. -/
theorem originalLeft : _root_.TopCat.homotopyPullbackComparison sq ≫
    _root_.TopCat.homotopyPullbackLeft p h = s :=
  _root_.TopCat.homotopyPullbackComparison_left sq

/-- The original whole right map survives the focused provider boundary. -/
theorem originalRight : _root_.TopCat.homotopyPullbackComparison sq ≫
    _root_.TopCat.homotopyPullbackRight p h = q :=
  _root_.TopCat.homotopyPullbackComparison_right sq

/-- The complete original target path is the original constant-path family. -/
theorem originalWholePath : _root_.TopCat.homotopyPullbackComparison sq ≫
    _root_.TopCat.homotopyPullbackPath p h = s ≫ p ≫ _root_.TopCat.pathConstant B :=
  _root_.TopCat.homotopyPullbackComparison_path sq

/-- Time zero is the actual image of the original left point. -/
theorem originalPathZero : _root_.TopCat.homotopyPullbackComparison sq ≫
    _root_.TopCat.homotopyPullbackPath p h ≫ _root_.TopCat.pathEvalZero B = s ≫ p := by
  simp

/-- Time one is the actual image of the original right point. -/
theorem originalPathOne : _root_.TopCat.homotopyPullbackComparison sq ≫
    _root_.TopCat.homotopyPullbackPath p h ≫ _root_.TopCat.pathEvalOne B = q ≫ h := by
  simpa using sq.w

end MathlibExtTest.Topology.Category.TopCat.HomotopyPullbackComparisonTests

end
