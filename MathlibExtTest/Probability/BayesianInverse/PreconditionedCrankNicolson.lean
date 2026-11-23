/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BayesianInverse.PreconditionedCrankNicolson
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.BayesianInverse

namespace MathlibExtTest.Probability.BayesianInverse.PreconditionedCrankNicolson

/-- The standard Gaussian on `ℝ` is centred. -/
lemma integral_id_std : (gaussianReal 0 1)[id] = 0 := by
  simp [integral_id_gaussianReal]

/-- pCN with step `β = 1/2` is reversible for the standard Gaussian on `ℝ`. -/
example : Kernel.IsReversible (pcnKernel (gaussianReal 0 1) (1 / 2)) (gaussianReal 0 1) :=
  isReversible_pcnKernel _ integral_id_std (by norm_num) (by norm_num)

/-- The standard Gaussian is invariant for pCN with `β = 1/2`. -/
example : Kernel.Invariant (pcnKernel (gaussianReal 0 1) (1 / 2)) (gaussianReal 0 1) :=
  invariant_pcnKernel _ integral_id_std (by norm_num) (by norm_num)

/-- The endpoint `β = 1` is the independence sampler: `v = ξ`. -/
example (p : ℝ × ℝ) : pcnProposal 1 p = p.2 := by simp [pcnProposal]

/-- The endpoint `β = 0` never moves. -/
example (p : ℝ × ℝ) : pcnProposal 0 p = p.1 := by simp [pcnProposal]

/-- Symmetry of the joint law of a pCN step on `ℝ` with `β = -3/5`. -/
example : (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun p ↦ (p.1, pcnProposal (-3 / 5) p))).map Prod.swap =
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map fun p ↦ (p.1, pcnProposal (-3 / 5) p) :=
  map_swap_pcn_eq _ integral_id_std (by norm_num) (by norm_num)

end MathlibExtTest.Probability.BayesianInverse.PreconditionedCrankNicolson
