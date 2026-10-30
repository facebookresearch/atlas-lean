/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CharFunStandardizedBinomial

@[expose] public section

open MeasureTheory Filter Complex ProbabilityTheory
open MathlibExt.Probability.CharFunStandardizedBinomial
open scoped unitInterval Topology

/-- Signature restatement: affine transformation of a characteristic function. -/
theorem charFun_map_affine_test (μ : Measure ℝ) (a s t : ℝ) :
    charFun (μ.map (fun x => (x - a) / s)) t =
      charFun μ (t * s⁻¹) * Complex.exp (↑(-(a * (t * s⁻¹))) * Complex.I) :=
  charFun_map_affine μ a s t

/-- Signature restatement: characteristic function of the binomial distribution. -/
theorem charFun_binomial_real_test (n : ℕ) (p : I) (t : ℝ) :
    charFun Bin(ℝ, n, p) t =
      ((1 - (p : ℝ)) + (p : ℝ) * Complex.exp (↑t * Complex.I)) ^ n :=
  charFun_binomial_real n p t

/-- The standardized binomial is a probability measure (the instance in the
main module). -/
theorem isProbabilityMeasure_standardizedBinomial_test (n : ℕ) (p : I) :
    IsProbabilityMeasure (standardizedBinomial n p) :=
  inferInstance

/-- Signature restatement: characteristic function of the standardized binomial. -/
theorem charFun_standardizedBinomial_test (n : ℕ) (p : I) (t : ℝ) :
    let s := Real.sqrt (↑n * ↑p * (1 - ↑p))
    charFun (standardizedBinomial n p) t =
      charFun Bin(ℝ, n, p) (t * s⁻¹) *
        Complex.exp (↑(-(↑n * (↑p : ℝ) * (t * s⁻¹))) * Complex.I) :=
  charFun_standardizedBinomial n p t

/-- Signature restatement: convergence of characteristic functions. -/
theorem tendsto_charFun_standardizedBinomial_test (p : I) (hp₀ : (0 : ℝ) < p)
    (hp₁ : (p : ℝ) < 1) (t : ℝ) :
    Tendsto (fun n ↦ charFun (standardizedBinomial n p) t) atTop
      (𝓝 (Complex.exp (-(t ^ 2 / 2)))) :=
  tendsto_charFun_standardizedBinomial p hp₀ hp₁ t

/-- The `n = 0` binomial distribution is the Dirac mass at `0`, so its
characteristic function is identically `1`. -/
theorem charFun_binomial_real_zero_test (p : I) (t : ℝ) :
    charFun Bin(ℝ, 0, p) t = 1 := by
  rw [charFun_binomial_real]
  simp

/-- The `n = 1` case of the binomial characteristic function: it is the
characteristic function of a Bernoulli variable. -/
theorem charFun_binomial_real_one_test (p : I) (t : ℝ) :
    charFun Bin(ℝ, 1, p) t = (1 - (p : ℝ)) + (p : ℝ) * Complex.exp (↑t * Complex.I) := by
  rw [charFun_binomial_real]
  simp

/-- The Taylor remainder bound at `z = 0` collapses to `0 ≤ 0`. -/
theorem exp_taylor2_err_zero_test :
    ‖Complex.exp 0 - 1 - (0 : ℂ) - (0 : ℂ) ^ 2 / 2‖ ≤ 2 * ‖(0 : ℂ)‖ ^ 3 :=
  exp_taylor2_err 0 (by simp)

/-- Concrete instance of the convergence theorem at `p = 1 / 2`. -/
theorem tendsto_charFun_standardizedBinomial_half_test (t : ℝ) :
    Tendsto
      (fun n ↦ charFun (standardizedBinomial n ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩) t)
      atTop (𝓝 (Complex.exp (-(t ^ 2 / 2)))) :=
  tendsto_charFun_standardizedBinomial _ (by norm_num) (by norm_num) t

#print axioms charFun_map_affine_test
#print axioms charFun_binomial_real_test
#print axioms charFun_standardizedBinomial_test
#print axioms tendsto_charFun_standardizedBinomial_test
