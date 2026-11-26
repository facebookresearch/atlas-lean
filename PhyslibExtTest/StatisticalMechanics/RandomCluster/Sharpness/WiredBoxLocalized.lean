/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WiredBoxLocalized

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WiredBoxLocalized`

On the doubled box in `d = 2`, `q = 2`, `β = 1`:
* `innerCrossInd_monotone` and `innerCrossInd_idem` for the inner crossing indicator;
* `wiredOuterInnerTheta_zero` and `wiredOuterInnerSig_pos`;
* `wiredOuterInnerDenom_pos`: the OSSS denominator is positive;
* `wired_outer_inner_hcov_sharp_of_comparison`, given its comparison hypothesis.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WiredBoxLocalized

open _root_.StatMech _root_.StatMech.OSSS
open Lattice RevealmentConstruction AdaptiveCovLowerGeom
open LocalizedCrossTree WiredBoxDifferential
open FK DecisionTree RevealmentTranslation WiredBoxLocalized

-- The inner crossing indicator is monotone and idempotent.
example (ω : ConfigSpace (boxGraph 2 (2 * 1)).edgeSet) :
    Monotone (innerCrossInd 2 1) ∧
      innerCrossInd 2 1 ω * innerCrossInd 2 1 ω = innerCrossInd 2 1 ω :=
  ⟨innerCrossInd_monotone 2 1, innerCrossInd_idem 2 1 ω⟩

-- The centered crossing profile is `1` at radius `0`, and its partial sums are positive.
example : wiredOuterInnerTheta 2 2 1 0 = 1 ∧ 0 < wiredOuterInnerSig 2 3 2 1 :=
  ⟨wiredOuterInnerTheta_zero 2 2 1 (by norm_num) one_pos,
    wiredOuterInnerSig_pos 2 3 (by norm_num) 2 1 (by norm_num) one_pos⟩

-- The OSSS denominator of the doubled box is positive.
example : 0 < wiredOuterInnerDenom 2 3 2 1 :=
  wiredOuterInnerDenom_pos 2 3 (by norm_num) 2 1 (by norm_num) one_pos

-- The sharp covariance bound, given the off-centre comparison hypothesis.
example (hcomp : ∀ x, x ∈ Percolation.boxFinset 2 3 → ∀ k, k ∈ Finset.Icc 1 (3 / 2) →
      wiredOuterInnerConn 2 3 2 1 x k ≤ wiredOuterInnerTheta 2 2 1 k) :=
  wired_outer_inner_hcov_sharp_of_comparison 2 3 (by norm_num) 2 1 (by norm_num) one_pos hcomp

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WiredBoxLocalized
