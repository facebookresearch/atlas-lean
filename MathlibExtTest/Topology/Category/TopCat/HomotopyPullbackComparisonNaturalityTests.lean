/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyPullbackComparisonNaturality

/-!
# Clients of original-square naturality and the stock point-fiber map

The whole original square maps and both source/target squares are retained.
The point-fiber client identifies the literal existing constant-path map.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace MathlibExtTest.Topology.Category.TopCat.HomotopyPullbackComparisonNaturalityTests

/-- Every original map in both squares appears in the actual naturality equation. -/
theorem originalSquaresNatural
    {A E W B A' E' W' B' : _root_.TopCat.{u}}
    {s : A ⟶ E} {q : A ⟶ W} {p : E ⟶ B} {h : W ⟶ B}
    {s' : A' ⟶ E'} {q' : A' ⟶ W'} {p' : E' ⟶ B'} {h' : W' ⟶ B'}
    (sq : CommSq s q p h) (sq' : CommSq s' q' p' h')
    (a : A ⟶ A') (e : E ⟶ E') (w : W ⟶ W') (b : B ⟶ B')
    (hs : s ≫ e = a ≫ s') (hq : q ≫ w = a ≫ q')
    (hp : p ≫ b = e ≫ p') (hh : h ≫ b = w ≫ h') :
    _root_.TopCat.homotopyPullbackComparison sq ≫
        _root_.TopCat.homotopyPullbackMap e w b hp hh =
      a ≫ _root_.TopCat.homotopyPullbackComparison sq' :=
  _root_.TopCat.homotopyPullbackComparison_naturality sq sq' a e w b hs hq hp hh

/-- The original strict point-fiber square keeps the existing literal comparison map. -/
theorem originalPointFiber {E B : _root_.TopCat.{u}} (p : E ⟶ B) (b : B) :
    _root_.TopCat.homotopyPullbackComparison
        (IsPullback.of_hasPullback p (_root_.TopCat.const (X := _root_.TopCat.of PUnit) b)).toCommSq =
      _root_.TopCat.strictFiberToHomotopyFiber p b :=
  _root_.TopCat.homotopyPullbackComparison_pointFiber p b

end MathlibExtTest.Topology.Category.TopCat.HomotopyPullbackComparisonNaturalityTests

end
