/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyPullbackComparison
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange

/-!
# Naturality of the stock constant-path comparison

The actual maps of strict squares preserve both original points and the
whole target path. On the original strict point-fiber square the same
comparison is the existing constant-path strict-fiber comparison.
These declarations and proofs are moved unchanged from
`HomotopyCartesianOpenCoverDescent`, preserving their original names.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat.modelCategory

universe u

namespace TopCat

private theorem pathConstant_naturality {B B' : TopCat.{u}} (f : B ⟶ B') :
    pathConstant B ≫ pathObjectMap f = f ≫ pathConstant B' := by
  ext x t
  rfl

/-- Constant-path square comparisons commute with their actual maps of squares. -/
theorem homotopyPullbackComparison_naturality
    {A E W B A' E' W' B' : TopCat.{u}}
    {s : A ⟶ E} {q : A ⟶ W} {p : E ⟶ B} {h : W ⟶ B}
    {s' : A' ⟶ E'} {q' : A' ⟶ W'} {p' : E' ⟶ B'} {h' : W' ⟶ B'}
    (sq : CommSq s q p h) (sq' : CommSq s' q' p' h')
    (a : A ⟶ A') (e : E ⟶ E') (w : W ⟶ W') (b : B ⟶ B')
    (hs : s ≫ e = a ≫ s') (hq : q ≫ w = a ≫ q')
    (hp : p ≫ b = e ≫ p') (hh : h ≫ b = w ≫ h') :
    homotopyPullbackComparison sq ≫ homotopyPullbackMap e w b hp hh =
      a ≫ homotopyPullbackComparison sq' := by
  apply homotopyPullback_hom_ext
  · rw [Category.assoc, homotopyPullbackMap_left, ← Category.assoc,
      homotopyPullbackComparison_left, hs, Category.assoc, homotopyPullbackComparison_left]
  · rw [Category.assoc, homotopyPullbackMap_right, ← Category.assoc,
      homotopyPullbackComparison_right, hq, Category.assoc, homotopyPullbackComparison_right]
  · have hbase : s ≫ p ≫ b = a ≫ s' ≫ p' := by
      rw [hp, ← Category.assoc, hs, Category.assoc]
    calc
      (homotopyPullbackComparison sq ≫ homotopyPullbackMap e w b hp hh) ≫
          homotopyPullbackPath p' h' =
          homotopyPullbackComparison sq ≫ homotopyPullbackPath p h ≫ pathObjectMap b := by
            rw [Category.assoc, homotopyPullbackMap_path]
      _ = s ≫ p ≫ pathConstant B ≫ pathObjectMap b := by
        rw [← Category.assoc, homotopyPullbackComparison_path]
        simp only [Category.assoc]
      _ = a ≫ s' ≫ p' ≫ pathConstant B' := by
        rw [pathConstant_naturality]
        exact (reassoc_of% hbase) (pathConstant B')
      _ = (a ≫ homotopyPullbackComparison sq') ≫ homotopyPullbackPath p' h' := by
        rw [Category.assoc, homotopyPullbackComparison_path]

/-- On the canonical strict point-fiber square this is the existing constant-path comparison. -/
theorem homotopyPullbackComparison_pointFiber {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :
    homotopyPullbackComparison
        (IsPullback.of_hasPullback p (TopCat.const (X := TopCat.of PUnit) b)).toCommSq =
      strictFiberToHomotopyFiber p b := by
  apply homotopyPullback_hom_ext
  · change _ ≫ homotopyFiberToTotal p b = _ ≫ homotopyFiberToTotal p b
    rw [homotopyPullbackComparison_left, strictFiberToHomotopyFiber_toTotal]
  · exact isTerminalPUnit.hom_ext _ _
  · rw [homotopyPullbackComparison_path, strictFiberToHomotopyFiber_path]
    exact (reassoc_of% (pullback.condition (f := p)
      (g := TopCat.const (X := TopCat.of PUnit) b))) (pathConstant B)

end TopCat

end
