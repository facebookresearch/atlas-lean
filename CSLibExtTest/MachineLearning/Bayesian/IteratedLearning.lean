/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Bayesian.IteratedLearning
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Tests for iterated learning: posterior sampling preserves the prior

Four boundary cases on two hypotheses and two observations (`Bool`/`Bool`):

* symmetric positive likelihoods: the prior is stationary and the chain is
  irreducible (every entry positive);
* identical likelihoods: data are uninformative, the chain forgets in one step;
* disjoint likelihood supports: the chain is the identity, so every
  distribution is stationary (stationarity is not unique convergence);
* the zero-mass prior `PMF.pure true`: it is stationary, and clearing the
  denominator holds at the datum `false`, whose predictive probability is `0`
  although the zero-mass hypothesis `false` gives it likelihood `1`.
-/

@[expose] public section

namespace CSLibExtTest.MachineLearning.Bayesian.IteratedLearning

open Cslib.MachineLearning.Bayesian.IteratedLearning
open scoped ENNReal NNReal

/-- Scalar sums used to check the `PMF.ofFintype` normalizations below. -/
theorem sum_half :
    ((1 / 2 : ℝ≥0) : ℝ≥0∞) + ((1 / 2 : ℝ≥0) : ℝ≥0∞) = 1 := by
  rw [← ENNReal.coe_add]
  norm_num

theorem sum_three_quarter :
    ((3 / 4 : ℝ≥0) : ℝ≥0∞) + ((1 / 4 : ℝ≥0) : ℝ≥0∞) = 1 := by
  rw [← ENNReal.coe_add]
  norm_num

/-- Uniform prior over two hypotheses. -/
noncomputable def priorUniform : PMF Bool :=
  PMF.ofFintype (fun _ : Bool => ((1 / 2 : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool]
    show ((1 / 2 : ℝ≥0) : ℝ≥0∞) + ((1 / 2 : ℝ≥0) : ℝ≥0∞) = 1
    exact sum_half)

/-- The uniform prior is everywhere positive. -/
theorem priorUniform_pos (h : Bool) : 0 < priorUniform h := by
  cases h <;> show (0 : ℝ≥0∞) < ((1 / 2 : ℝ≥0) : ℝ≥0∞)
  · exact ENNReal.coe_pos.mpr (by norm_num)
  · exact ENNReal.coe_pos.mpr (by norm_num)

/-- Symmetric positive likelihoods: matching observation with probability
`3/4`, mismatch with `1/4`. -/
noncomputable def likelihoodSymm : Bool → PMF Bool
  | true => PMF.ofFintype
      (fun b => if b then ((3 / 4 : ℝ≥0) : ℝ≥0∞) else ((1 / 4 : ℝ≥0) : ℝ≥0∞))
      (by
        rw [Fintype.sum_bool]
        show ((3 / 4 : ℝ≥0) : ℝ≥0∞) + ((1 / 4 : ℝ≥0) : ℝ≥0∞) = 1
        exact sum_three_quarter)
  | false => PMF.ofFintype
      (fun b => if b then ((1 / 4 : ℝ≥0) : ℝ≥0∞) else ((3 / 4 : ℝ≥0) : ℝ≥0∞))
      (by
        rw [Fintype.sum_bool]
        show ((1 / 4 : ℝ≥0) : ℝ≥0∞) + ((3 / 4 : ℝ≥0) : ℝ≥0∞) = 1
        rw [add_comm]
        exact sum_three_quarter)

/-- The symmetric likelihoods are everywhere positive. -/
theorem likelihoodSymm_pos (h d : Bool) : 0 < likelihoodSymm h d := by
  cases h <;> cases d <;> exact ENNReal.coe_pos.mpr (by norm_num)

/-- Boundary case 1: with positive likelihoods the prior is stationary. -/
theorem stationary_symmetric :
    priorUniform.bind
        (transmissionKernel Bool Bool priorUniform likelihoodSymm)
      = priorUniform :=
  transmission_stationary Bool Bool priorUniform likelihoodSymm

/-- Boundary case 1: with positive likelihoods the chain is irreducible. -/
theorem irreducible_symmetric (h h' : Bool) :
    0 < transmissionKernel Bool Bool priorUniform likelihoodSymm h h' :=
  transmissionKernel_pos Bool Bool priorUniform likelihoodSymm
    priorUniform_pos likelihoodSymm_pos h h'

/-- A fair coin, the uninformative datum. -/
noncomputable def fairCoin : PMF Bool :=
  PMF.ofFintype (fun _ : Bool => ((1 / 2 : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool]
    show ((1 / 2 : ℝ≥0) : ℝ≥0∞) + ((1 / 2 : ℝ≥0) : ℝ≥0∞) = 1
    exact sum_half)

/-- Hypothesis-independent likelihoods: data carry no information. -/
noncomputable def likelihoodConst : Bool → PMF Bool := fun _ => fairCoin

/-- Boundary case 2: with uninformative data the chain forgets in one step. -/
theorem forgets_in_one_step (h : Bool) :
    transmissionKernel Bool Bool priorUniform likelihoodConst h
      = priorUniform :=
  transmissionKernel_eq_prior Bool Bool priorUniform likelihoodConst
    fairCoin (fun _ => rfl) h

/-- Noiseless likelihoods: each hypothesis produces its own datum only. -/
noncomputable def likelihoodNoiseless : Bool → PMF Bool
  | true => PMF.pure true
  | false => PMF.pure false

/-- Noiseless likelihoods have disjoint supports. -/
theorem likelihoodNoiseless_disjoint (h₁ h₂ : Bool) (d : Bool)
    (hne : h₁ ≠ h₂) (hd : likelihoodNoiseless h₁ d ≠ 0) :
    likelihoodNoiseless h₂ d = 0 := by
  cases h₁ <;> cases h₂ <;> cases d <;>
    simp_all [likelihoodNoiseless, PMF.pure_apply]

/-- Boundary case 3: with disjoint supports the chain is the identity. -/
theorem identity_kernel (h : Bool) :
    transmissionKernel Bool Bool priorUniform likelihoodNoiseless h
      = PMF.pure h :=
  transmissionKernel_eq_pure Bool Bool priorUniform likelihoodNoiseless
    priorUniform_pos likelihoodNoiseless_disjoint h

/-- Boundary case 3: every distribution is stationary, so stationarity does not
imply convergence to the prior. -/
theorem identity_stationary (σ : PMF Bool) :
    σ.bind (transmissionKernel Bool Bool priorUniform likelihoodNoiseless)
      = σ :=
  bind_eq_of_eq_pure Bool _ (fun h => identity_kernel h) σ

/-- Boundary case 4: the zero-mass prior `PMF.pure true` is stationary. -/
theorem sparse_prior_stationary :
    (PMF.pure true).bind
        (transmissionKernel Bool Bool (PMF.pure true) likelihoodSymm)
      = PMF.pure true :=
  transmission_stationary Bool Bool (PMF.pure true) likelihoodSymm

/-- Boundary case 4: detailed balance under the zero-mass prior. -/
theorem sparse_prior_detailedBalance (h h' : Bool) :
    (PMF.pure true) h * transmissionKernel Bool Bool (PMF.pure true) likelihoodSymm h h' =
      (PMF.pure true) h' *
        transmissionKernel Bool Bool (PMF.pure true) likelihoodSymm h' h :=
  transmission_detailedBalance Bool Bool (PMF.pure true) likelihoodSymm h h'

/-- Boundary case 4 (zero-mass-prior regression): under the prior `PMF.pure true`
and noiseless likelihoods, the datum `false` has predictive probability `0`, yet
the zero-mass hypothesis `false` gives it likelihood `1`; clearing the
denominator still holds there, with both sides `0`. -/
theorem sparse_prior_zero_predictive :
    predictive Bool Bool (PMF.pure true) likelihoodNoiseless false = 0 ∧
      likelihoodNoiseless false false = 1 ∧
      predictive Bool Bool (PMF.pure true) likelihoodNoiseless false *
          posterior Bool Bool (PMF.pure true) likelihoodNoiseless false false =
        (PMF.pure true) false * likelihoodNoiseless false false := by
  refine ⟨?_, ?_, posterior_mul_predictive Bool Bool _ _ false false⟩
  · rw [predictive_apply, Fintype.sum_bool]
    simp [likelihoodNoiseless, PMF.pure_apply]
  · simp [likelihoodNoiseless, PMF.pure_apply]

end CSLibExtTest.MachineLearning.Bayesian.IteratedLearning
