/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.PoissonWeakConvergence

/-!
# Tests: Poisson convergence in law

Signature restatements of the theorems in
`MathlibExt.Probability.PoissonWeakConvergence`, a concrete evaluation of the
approximating success probability at `λ = 2, n = 2`, and `#print axioms` checks.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal unitInterval
open MathlibExt.Probability.PoissonWeakConvergence

namespace MathlibExtTest.Probability.PoissonWeakConvergence

/-- Signature restatement: characteristic function of a binomial law. -/
theorem charFun_binomialProbMeasure_test (n : ℕ) (p : I) (t : ℝ) :
    charFun (binomialProbMeasure n p : Measure ℝ) t =
      ((1 - (p : ℝ)) + (p : ℝ) * Complex.exp (↑t * Complex.I)) ^ n :=
  charFun_binomialProbMeasure n p t

/-- Signature restatement: characteristic function of a Poisson law. -/
theorem charFun_poissonProbMeasure_test (lam : ℝ≥0) (t : ℝ) :
    charFun (poissonProbMeasure lam : Measure ℝ) t =
      Complex.exp (↑lam * (Complex.exp (↑t * Complex.I) - 1)) :=
  charFun_poissonProbMeasure lam t

/-- Signature restatement: `n * (λ / (n + λ)) → λ`. -/
theorem tendsto_mul_poissonApproxProb_test (lam : ℝ≥0) :
    Tendsto (fun n : ℕ => (n : ℝ) * (poissonApproxProb lam n : ℝ)) atTop
      (𝓝 (lam : ℝ)) :=
  tendsto_mul_poissonApproxProb lam

/-- Signature restatement: characteristic functions of the approximating binomial
laws converge pointwise to the Poisson characteristic function. -/
theorem tendsto_charFun_binomialPoissonApprox_test (lam : ℝ≥0) (t : ℝ) :
    Tendsto (fun n => charFun (binomialPoissonApprox lam n : Measure ℝ) t) atTop
      (𝓝 (charFun (poissonProbMeasure lam : Measure ℝ) t)) :=
  tendsto_charFun_binomialPoissonApprox lam t

/-- Signature restatement: Poisson convergence in law. -/
theorem tendsto_binomialPoissonApprox_test (lam : ℝ≥0) :
    Tendsto (fun n => binomialPoissonApprox lam n) atTop
      (𝓝 (poissonProbMeasure lam)) :=
  tendsto_binomialPoissonApprox lam

/-- Concrete evaluation: at `λ = 2, n = 2` the approximating success probability
is `2 / (2 + 2) = 1 / 2`. -/
theorem poissonApproxProb_two_two :
    (poissonApproxProb 2 2 : ℝ) = 1 / 2 := by
  show (2 : ℝ) / ((2 : ℝ) + (2 : ℝ)) = 1 / 2
  norm_num

/-- At `t = 0` every characteristic function in the approximation equals `1`. -/
theorem charFun_binomialPoissonApprox_zero (lam : ℝ≥0) (n : ℕ) :
    charFun (binomialPoissonApprox lam n : Measure ℝ) 0 = 1 := by
  show charFun (binomialProbMeasure n (poissonApproxProb lam n) : Measure ℝ) 0 = 1
  rw [charFun_binomialProbMeasure]
  simp

#print axioms tendsto_binomialPoissonApprox
#print axioms charFun_binomialProbMeasure
#print axioms charFun_poissonProbMeasure

end MathlibExtTest.Probability.PoissonWeakConvergence
