/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BayesianInverse.MetropolisHastings
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.BayesianInverse

namespace MathlibExtTest.Probability.BayesianInverse.MetropolisHastings

private lemma integral_id_std : (gaussianReal 0 1)[id] = 0 := by
  simp [integral_id_gaussianReal]

/-- pCN for the posterior of `y = u³ + η` with data `y = 1` and a standard Gaussian prior
on `ℝ`: reversible for the posterior. -/
example : (mhKernel (pcnKernel (gaussianReal 0 1) (1 / 2)) fun u ↦ (1 - u ^ 3) ^ 2 / 2)
    |>.IsReversible (posterior (gaussianReal 0 1) fun u ↦ (1 - u ^ 3) ^ 2 / 2) :=
  isReversible_pcn_mhKernel _ integral_id_std (by norm_num) (by norm_num) (by fun_prop)

/-- The same chain leaves the posterior invariant. -/
example : (mhKernel (pcnKernel (gaussianReal 0 1) (1 / 2)) fun u ↦ (1 - u ^ 3) ^ 2 / 2)
    |>.Invariant (posterior (gaussianReal 0 1) fun u ↦ (1 - u ^ 3) ^ 2 / 2) :=
  invariant_mhKernel _ _ (isReversible_pcnKernel _ integral_id_std (by norm_num) (by norm_num))
    (by fun_prop)

/-- The Metropolis–Hastings kernel is Markov. -/
example : IsMarkovKernel
    (mhKernel (pcnKernel (gaussianReal 0 1) (1 / 2)) fun u ↦ (1 - u ^ 3) ^ 2 / 2) :=
  isMarkovKernel_mhKernel _ (by fun_prop)

/-- A move downhill in the potential is always accepted. -/
example (Φ : ℝ → ℝ) (u v : ℝ) (h : Φ v ≤ Φ u) : mhAcceptPotential Φ u v = 1 := by
  rw [mhAcceptPotential, min_eq_left (Real.one_le_exp (sub_nonneg.2 h)), ENNReal.ofReal_one]

end MathlibExtTest.Probability.BayesianInverse.MetropolisHastings
