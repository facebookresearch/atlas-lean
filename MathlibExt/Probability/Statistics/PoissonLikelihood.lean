/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Tactic.Ring

/-!
# The log-likelihood of independent Poisson counts

For counts `k : ι → ℕ` with means `E : ι → ℝ` over a finite index type,
`poissonLogLik E k = ∑ᵢ (kᵢ log Eᵢ - Eᵢ - log kᵢ!)`.

## Main results

* `pi_poissonMeasure_real_singleton`: the joint law `Measure.pi fun i => poissonMeasure (E i)` of
  independent Poisson counts gives the count vector `k` the probability
  `∏ᵢ e^{-Eᵢ} Eᵢ ^ {kᵢ} / kᵢ!`.
* `log_pi_poissonMeasure_real_singleton`: for positive means, the log-probability of `k` under
  that joint law is `poissonLogLik E k`.

These declarations are shared: the Poisson-random-field likelihood of
`MathlibExt.Biology.PopulationGenetics.DistributionOfFitnessEffects` re-exports them, and the
canonical Poisson GLM likelihood `MathlibExt.Probability.Statistics.GLM.poissonLogLik` is
`poissonLogLik` at the means `exp ηᵢ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace MathlibExt.Probability.Statistics.PoissonLikelihood

variable {ι : Type*} [Fintype ι]

/-- The Poisson log-likelihood `∑ (k_i log E_i - E_i - log k_i!)` of counts `k_i` with means
`E_i`. Meaningful for `E_i > 0`; at `E_i = 0` Lean's `log 0 = 0` gives a junk value. -/
noncomputable def poissonLogLik (E : ι → ℝ) (k : ι → ℕ) : ℝ :=
  ∑ i, ((k i : ℝ) * log (E i) - E i - log (Nat.factorial (k i)))

/-- The joint law of independent Poisson counts with means `E_i` gives the count vector `k`
the probability `∏ e^{-E_i} E_i ^ {k_i} / (k_i!)`. -/
theorem pi_poissonMeasure_real_singleton (E : ι → ℝ≥0) (k : ι → ℕ) :
    (Measure.pi fun i => poissonMeasure (E i)).real {k} =
      ∏ i, exp (-(E i : ℝ)) * (E i : ℝ) ^ k i / Nat.factorial (k i) := by
  classical
  rw [measureReal_def, ← Set.univ_pi_singleton k, Measure.pi_pi, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun i _ => poissonMeasure_real_singleton (E i) (k i)

/-- **The log-likelihood of independent Poisson counts.** For independent Poisson counts with
positive means `E_i`, the log-probability of the observed counts `k` is `poissonLogLik E k`. -/
theorem log_pi_poissonMeasure_real_singleton (E : ι → ℝ≥0) (hE : ∀ i, 0 < E i) (k : ι → ℕ) :
    log ((Measure.pi fun i => poissonMeasure (E i)).real {k}) =
      poissonLogLik (fun i => (E i : ℝ)) k := by
  classical
  have hpos (i : ι) : 0 < (E i : ℝ) := hE i
  have hfac (i : ι) : 0 < (Nat.factorial (k i) : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [pi_poissonMeasure_real_singleton, Real.log_prod]
  · unfold poissonLogLik
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.log_div (ne_of_gt (mul_pos (exp_pos _) (pow_pos (hpos i) _)))
        (ne_of_gt (hfac i)),
      Real.log_mul (ne_of_gt (exp_pos _)) (ne_of_gt (pow_pos (hpos i) _)),
      Real.log_exp, Real.log_pow]
    ring
  · intro i _
    exact ne_of_gt (div_pos (mul_pos (exp_pos _) (pow_pos (hpos i) _)) (hfac i))

end MathlibExt.Probability.Statistics.PoissonLikelihood
