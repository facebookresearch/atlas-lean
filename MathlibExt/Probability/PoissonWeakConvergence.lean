/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

import MathlibExt.Probability.CharFunStandardizedBinomial

/-!
# Poisson convergence in law

The Poisson limit theorem in its weak-convergence form: the binomial laws
`Bin(n, λ / (n + λ))` converge weakly to the Poisson law of rate `λ` as
`n → ∞`.

Source: `v1/Atlas/TheoryOfProbability/code/PoissonConvergence.lean`,
`poisson_convergence` (Lecture 17). In v1 the Poisson convergence theorem is
stated as pointwise convergence of the probability mass functions for a
triangular array of Bernoulli variables, and its analytic core
(`elem_symm_poly_tendsto_poisson`) was left unproved there; batch 30 (#423)
proved that core, and batch 19 (#364) proved the Bernoulli-sum pmf formula.
The weak-convergence form proved here is not stated in v1 and is not in
batches 19 or 30: it is proved directly from the characteristic functions via
Lévy's continuity theorem, so it needs neither the Bernoulli-sum pmf formula
nor the elementary-symmetric-polynomial core.

The binomial characteristic function is obtained from the existing
`CharFunStandardizedBinomial.charFun_binomial_real` theorem.

The choice `pₙ = λ / (n + λ)` is the standard one-parameter family with
`n pₙ → λ` and `pₙ ∈ [0, 1]` for every `n` (including `n = 0`, where the
formula gives `p₀ = 0` when `λ = 0` and `p₀ = 1` otherwise, by division);
any family with `n pₙ → λ` would give the same limit by the same argument.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal unitInterval

namespace MathlibExt.Probability.PoissonWeakConvergence

/-- The binomial law `Bin(n, p)` on `ℝ`, bundled as a probability measure. -/
noncomputable def binomialProbMeasure (n : ℕ) (p : I) : ProbabilityMeasure ℝ :=
  ⟨Bin(ℝ, n, p), inferInstance⟩

/-- The Poisson law of rate `λ` on `ℝ`, bundled as a probability measure. -/
noncomputable def poissonProbMeasure (lam : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨Po(ℝ, lam), inferInstance⟩

/-- The success probability `λ / (n + λ)` used in the binomial approximation to
the Poisson law. It lies in `[0, 1]` for every `n`, and `n * pₙ → λ`. -/
noncomputable def poissonApproxProb (lam : ℝ≥0) (n : ℕ) : I :=
  ⟨(lam : ℝ) / ((n : ℝ) + (lam : ℝ)),
    ⟨div_nonneg lam.coe_nonneg (by positivity),
     div_le_one_of_le₀ (by
       have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
       linarith) (by positivity)⟩⟩

/-- The binomial law `Bin(n, λ / (n + λ))` on `ℝ`. -/
noncomputable def binomialPoissonApprox (lam : ℝ≥0) (n : ℕ) : ProbabilityMeasure ℝ :=
  binomialProbMeasure n (poissonApproxProb lam n)

/-- **Characteristic function of a binomial law.**
`φ_{Bin(n, p)}(t) = ((1 - p) + p * e^{it})ⁿ`. -/
theorem charFun_binomialProbMeasure (n : ℕ) (p : I) (t : ℝ) :
    charFun (binomialProbMeasure n p : Measure ℝ) t =
      ((1 - (p : ℝ)) + (p : ℝ) * Complex.exp (↑t * Complex.I)) ^ n := by
  show charFun (Bin(ℝ, n, p)) t = _
  exact MathlibExt.Probability.CharFunStandardizedBinomial.charFun_binomial_real n p t

/-- **Characteristic function of a Poisson law.**
`φ_{Poisson(λ)}(t) = exp(λ * (e^{it} - 1))`. -/
theorem charFun_poissonProbMeasure (lam : ℝ≥0) (t : ℝ) :
    charFun (poissonProbMeasure lam : Measure ℝ) t =
      Complex.exp (↑lam * (Complex.exp (↑t * Complex.I) - 1)) :=
  charFun_map_cast_poissonMeasure lam t

/-- The expected number of successes tends to the rate: `n * (λ / (n + λ)) → λ`. -/
theorem tendsto_mul_poissonApproxProb (lam : ℝ≥0) :
    Tendsto (fun n : ℕ => (n : ℝ) * (poissonApproxProb lam n : ℝ)) atTop
      (𝓝 (lam : ℝ)) := by
  have htop : Tendsto (fun n : ℕ => (n : ℝ) + (lam : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n => le_add_of_nonneg_right lam.coe_nonneg)
      tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + (lam : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp htop
  have hkey : Tendsto (fun n : ℕ => (lam : ℝ) -
      (lam : ℝ) ^ 2 * ((n : ℝ) + (lam : ℝ))⁻¹) atTop (𝓝 (lam : ℝ)) := by
    simpa using tendsto_const_nhds.sub
      ((tendsto_const_nhds (x := (lam : ℝ) ^ 2)).mul hinv)
  refine hkey.congr' (Filter.Eventually.of_forall fun n => ?_)
  show (lam : ℝ) - (lam : ℝ) ^ 2 * ((n : ℝ) + (lam : ℝ))⁻¹ =
    (n : ℝ) * (poissonApproxProb lam n : ℝ)
  show (lam : ℝ) - (lam : ℝ) ^ 2 * ((n : ℝ) + (lam : ℝ))⁻¹ =
    (n : ℝ) * ((lam : ℝ) / ((n : ℝ) + (lam : ℝ)))
  by_cases h : (n : ℝ) + (lam : ℝ) = 0
  · have hlam : (lam : ℝ) = 0 := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hlam' : (0 : ℝ) ≤ (lam : ℝ) := lam.coe_nonneg
      linarith
    rw [hlam]
    simp
  · field_simp
    ring

/-- The characteristic functions of the approximating binomial laws converge
pointwise to the characteristic function of the Poisson law. -/
theorem tendsto_charFun_binomialPoissonApprox (lam : ℝ≥0) (t : ℝ) :
    Tendsto (fun n => charFun (binomialPoissonApprox lam n : Measure ℝ) t) atTop
      (𝓝 (charFun (poissonProbMeasure lam : Measure ℝ) t)) := by
  rw [charFun_poissonProbMeasure]
  have hrewrite : ∀ n : ℕ,
      charFun (binomialPoissonApprox lam n : Measure ℝ) t =
        (1 + (poissonApproxProb lam n : ℝ) *
          (Complex.exp (↑t * Complex.I) - 1)) ^ n := by
    intro n
    show charFun (binomialProbMeasure n (poissonApproxProb lam n) : Measure ℝ) t = _
    rw [charFun_binomialProbMeasure]
    congr 1
    ring
  simp_rw [hrewrite]
  apply Complex.tendsto_one_add_pow_exp_of_tendsto
  have hnpC : Tendsto (fun n : ℕ => (n : ℂ) * ((poissonApproxProb lam n : ℝ) : ℂ))
      atTop (𝓝 ((lam : ℝ) : ℂ)) := by
    have h0 : Tendsto (fun n : ℕ => (((n : ℝ) * (poissonApproxProb lam n : ℝ) : ℝ) : ℂ))
        atTop (𝓝 (((lam : ℝ) : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (lam : ℝ)).comp
        (tendsto_mul_poissonApproxProb lam)
    refine h0.congr' (Filter.Eventually.of_forall fun n => ?_)
    push_cast
    ring
  have h : Tendsto (fun n : ℕ => ((n : ℂ) * ((poissonApproxProb lam n : ℝ) : ℂ)) *
      (Complex.exp (↑t * Complex.I) - 1)) atTop
      (𝓝 (((lam : ℝ) : ℂ) * (Complex.exp (↑t * Complex.I) - 1))) :=
    hnpC.mul tendsto_const_nhds
  refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
  show ((n : ℂ) * ((poissonApproxProb lam n : ℝ) : ℂ)) *
      (Complex.exp (↑t * Complex.I) - 1) =
    (n : ℂ) * (((poissonApproxProb lam n : ℝ) : ℂ) *
      (Complex.exp (↑t * Complex.I) - 1))
  ring

/-- **Poisson convergence in law (binomial approximation).** The binomial laws
`Bin(n, λ / (n + λ))` converge weakly to the Poisson law of rate `λ`. -/
theorem tendsto_binomialPoissonApprox (lam : ℝ≥0) :
    Tendsto (fun n => binomialPoissonApprox lam n) atTop
      (𝓝 (poissonProbMeasure lam)) := by
  rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro t
  exact tendsto_charFun_binomialPoissonApprox lam t

end MathlibExt.Probability.PoissonWeakConvergence
