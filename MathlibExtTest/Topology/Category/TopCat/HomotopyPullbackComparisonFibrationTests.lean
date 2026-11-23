/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyPullbackComparisonFibration
public import MathlibExt.Topology.Category.TopCat.HomotopyPullbackComparisonNaturality

/-!
# Clients of the original strict-pullback fibration criterion

Only the actual original pullback and projection fibration are inputs.
The conclusion retains the literal stock comparison and the old point-fiber map.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat.modelCategory

universe u

namespace MathlibExtTest.Topology.Category.TopCat.HomotopyPullbackComparisonFibrationTests

/-- The original arbitrary pullback square and actual projection fibration
earn weakness of the same stock comparison. -/
theorem originalPullbackWeak
    {A E W B : _root_.TopCat.{u}} {s : A ⟶ E} {q : A ⟶ W}
    {p : E ⟶ B} {h : W ⟶ B} (sq : IsPullback s q p h) [Fibration p] :
    _root_.TopCat.weakHomotopyEquivalences (_root_.TopCat.homotopyPullbackComparison sq.toCommSq) :=
  _root_.TopCat.homotopyPullbackComparison_mem_of_isPullback sq

/-- The canonical strict pullback preserves both original arbitrary legs. -/
theorem canonicalPullbackWeak {E W B : _root_.TopCat.{u}}
    (p : E ⟶ B) (h : W ⟶ B) [Fibration p] :
    _root_.TopCat.weakHomotopyEquivalences (_root_.TopCat.homotopyPullbackComparison
      (IsPullback.of_hasPullback p h).toCommSq) :=
  _root_.TopCat.homotopyPullbackComparison_mem_of_isPullback (IsPullback.of_hasPullback p h)

/-- Naturality's point-fiber readout keeps the actual old fiber comparison
in the fibration criterion's weak conclusion. -/
theorem originalPointFiberWeak {E B : _root_.TopCat.{u}}
    (p : E ⟶ B) (b : B) [Fibration p] :
    _root_.TopCat.weakHomotopyEquivalences (_root_.TopCat.strictFiberToHomotopyFiber p b) := by
  have h := _root_.TopCat.homotopyPullbackComparison_mem_of_isPullback
    (IsPullback.of_hasPullback p (_root_.TopCat.const (X := _root_.TopCat.of PUnit) b))
  rw [_root_.TopCat.homotopyPullbackComparison_pointFiber] at h
  exact h

end MathlibExtTest.Topology.Category.TopCat.HomotopyPullbackComparisonFibrationTests

end
