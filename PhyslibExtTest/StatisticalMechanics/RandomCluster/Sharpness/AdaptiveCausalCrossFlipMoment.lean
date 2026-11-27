/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalCrossFlipMoment

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalCrossFlipMoment`

* `cross_flip_moment_extendDecisionTreeTriple_eq` for the random-cluster mass on the complete
  graph on `Fin 2` at `p = 1/2`, `q = 2`, with the one-query decision tree on `s(0, 1)`,
  phase `0` and flipped edge `s(0, 1)`;
* the same identity for a constant leaf tree at an arbitrary phase.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalCrossFlipMoment

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptiveCausalKernel
open _root_.StatMech.OSSS.MonotonicFK

-- The cross-flip moment identity for the one-query tree on `K₂`.
example (seed : ConfigSpace (Sym2 (Fin 2))) :
    (∑ base,
      (if tripleModeAt (extendDecisionTreeTriple (some 0)
          (.node s(0, 1) (.leaf true) (.leaf false)) seed Finset.univ) base s(0, 1) = .flip
        then 1 else 0) *
        (∑ left, ∑ right,
          (DecisionTree.evalR (.node s(0, 1) (.leaf true) (.leaf false)) left *
              Lindeberg.coord s(0, 1) right +
            DecisionTree.evalR (.node s(0, 1) (.leaf true) (.leaf false)) right *
              Lindeberg.coord s(0, 1) left) *
            crossTripleJointProb (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) ∅ base left right
              (extendDecisionTreeTriple (some 0) (.node s(0, 1) (.leaf true) (.leaf false)) seed
                Finset.univ))) =
      2 * (Lindeberg.mean (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
          (DecisionTree.evalR (.node s(0, 1) (.leaf true) (.leaf false))) *
        Lindeberg.mean (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) (Lindeberg.coord s(0, 1))) *
          flipBaseProb (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) ∅ seed s(0, 1)
            (extendDecisionTreeTriple (some 0) (.node s(0, 1) (.leaf true) (.leaf false)) seed
              Finset.univ) :=
  cross_flip_moment_extendDecisionTreeTriple_eq _
    (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num)) _ seed 0 s(0, 1)

-- The identity for a constant leaf tree, at any phase and flipped edge.
example (seed : ConfigSpace (Sym2 (Fin 2))) (t : ℕ) (e : Sym2 (Fin 2)) :=
  cross_flip_moment_extendDecisionTreeTriple_eq (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
    (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num)) (.leaf true) seed t e

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalCrossFlipMoment
