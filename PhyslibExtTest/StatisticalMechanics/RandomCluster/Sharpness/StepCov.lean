/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.StepCov

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.StepCov`

* the refutation `stepCovBound_no_factor_false` of the one-copy step bound, restated;
* the explicit values `mean muU fAvg = 1/2` and `Cov(fAvg, ω false) = 1/8` of the
  counterexample, and its depth-one tree `Tw` queries `false` first;
* `stepCovBoundTwo_of_cplFKG` and `tree_osss_sharp` in their conditional forms.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.StepCov

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.StepCov
open _root_.StatMech.OSSS.StepCov.Counterexample
open _root_.StatMech.OSSS.Lindeberg _root_.StatMech.OSSS.LindebergTree
open _root_.StatMech.OSSS.DecisionTree

-- The one-copy step bound fails for the uniform measure on two bits.
example : ¬ StepCovBound muU Tw fAvg := stepCovBound_no_factor_false

-- The counterexample's mean and covariance.
example : mean muU fAvg = 1 / 2 ∧ Lindeberg.cov muU fAvg (coord false) = 1 / 8 :=
  ⟨mean_fAvg, cov_fAvg⟩

-- The counterexample tree queries the bit `false` first, which is fresh at step `0`.
example (ω : ConfigSpace Bool) : pathPrefix Tw ω 1 = {false} ∧ freshAt Tw ω 0 false = 1 :=
  ⟨pathPrefix_Tw_one ω, freshAt_Tw_zero ω⟩

-- The two-copy step bound from the coupled residue condition.
example {E : Type*} [Fintype E] [DecidableEq E] {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hFKG : FKGLatticeCondition μ) (T : DecisionTree E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (hf0 : 0 ≤ f) (hres : ∀ t e, StepCovResidue μ T f t e) :
    StepCovBoundTwo μ T f :=
  stepCovBoundTwo_of_cplFKG hpos hFKG T hf hf0 hres

-- Decision-tree OSSS, conditional on the residue condition.
example {E : Type*} [Fintype E] [DecidableEq E] {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) (T : DecisionTree E)
    (hfmono : Monotone T.evalR) (hres : ∀ t e, StepCovResidue μ T T.evalR t e) :
    Lindeberg.var μ T.evalR ≤ ∑ e, revealmentMu μ T e * Lindeberg.cov μ T.evalR (coord e) :=
  tree_osss_sharp hpos hμ1 hFKG T hfmono hres

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.StepCov
