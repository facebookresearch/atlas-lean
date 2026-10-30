/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.PopulationGenetics.Diffusion.Mutation

/-! Tests for the Wright–Fisher diffusion with mutation: the neutral special case, concrete
stationary moments (uniform and symmetric Beta laws), weak stationarity for a polynomial test
function, the zero-flux identity at a point, one generation of the chain (drift and scaled second
moment), and a junk value
outside the parameter domain `θ₁, θ₂ > 0`. -/

open Real Set MeasureTheory ProbabilityTheory

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.Mutation

open MathlibExt.Biology.PopulationGenetics.Diffusion

/-- Without mutation the generator is the neutral one; e.g. heterozygosity decays at rate `1`. -/
example (x : ℝ) :
    mutationGenerator 0 0 (fun y => 2 * y * (1 - y)) x = -(2 * x * (1 - x)) := by
  rw [mutationGenerator_heterozygosity]
  ring

/-- Constants are annihilated by the generator. -/
example (θ₁ θ₂ c x : ℝ) : mutationGenerator θ₁ θ₂ (fun _ => c) x = 0 := by
  simp [mutationGenerator]

/-- The mutation drift vanishes at the deterministic equilibrium `x = θ₁ / (θ₁ + θ₂)`. -/
example : mutationGenerator 1 3 id (1 / 4) = 0 := by
  rw [mutationGenerator_id]
  norm_num

/-- `θ₁ = θ₂ = 1`: Wright's law is uniform, with mean `1/2`. -/
example : ∫ x, x ∂(betaMeasure 1 1) = 1 / 2 := by
  rw [integral_id_betaMeasure one_pos one_pos]
  norm_num

/-- `θ₁ = θ₂ = 1`: the uniform law has expected heterozygosity `2 (1/2 - 1/3) = 1/3`. -/
example : ∫ x, 2 * x * (1 - x) ∂(betaMeasure 1 1) = 1 / 3 := by
  rw [integral_heterozygosity_betaMeasure one_pos one_pos]
  norm_num

/-- Asymmetric rates `θ₁ = 1`, `θ₂ = 3`: mean `1/4`, heterozygosity `2 · 3 / (4 · 5) = 3/10`. -/
example : ∫ x, x ∂(betaMeasure 1 3) = 1 / 4 ∧
    ∫ x, 2 * x * (1 - x) ∂(betaMeasure 1 3) = 3 / 10 := by
  rw [integral_id_betaMeasure one_pos (by norm_num),
    integral_heterozygosity_betaMeasure one_pos (by norm_num)]
  norm_num

/-- Small mutation rates (`θ₁ = θ₂ = 1/10`) give little heterozygosity: `1/12`. -/
example : ∫ x, 2 * x * (1 - x) ∂(betaMeasure (1 / 10) (1 / 10)) = 1 / 12 := by
  rw [integral_heterozygosity_betaMeasure (by norm_num) (by norm_num)]
  norm_num

/-- Weak stationarity for the test function `x ↦ x ^ 3` (a smooth function on `ℝ`). -/
example : ∫ x, mutationGenerator 2 5 (fun y => y ^ 3) x ∂(betaMeasure 2 5) = 0 :=
  integral_mutationGenerator_betaMeasure (by norm_num) (by norm_num)
    ((contDiff_id.pow 3).contDiffOn)

/-- Weak stationarity in density form, with the accompanying integrability. -/
example (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Icc 0 1)) :
    IntervalIntegrable (fun x => mutationGenerator 1 1 f x * betaPDFReal 1 1 x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, mutationGenerator 1 1 f x * betaPDFReal 1 1 x = 0 :=
  ⟨intervalIntegrable_mutationGenerator_mul_betaPDFReal one_pos one_pos hf,
    integral_mutationGenerator_mul_betaPDFReal one_pos one_pos hf⟩

/-- Zero flux and the forward equation at the midpoint for `θ₁ = 2`, `θ₂ = 3`. -/
example :
    deriv (fun y => y * (1 - y) * betaPDFReal 2 3 y) (1 / 2) / 2 -
        (2 * (1 - 1 / 2) - 3 * (1 / 2)) / 2 * betaPDFReal 2 3 (1 / 2) = 0 ∧
      deriv (deriv (fun y => y * (1 - y) * betaPDFReal 2 3 y)) (1 / 2) / 2 -
        deriv (fun y => (2 * (1 - y) - 3 * y) / 2 * betaPDFReal 2 3 y) (1 / 2) = 0 :=
  ⟨flux_betaPDFReal 2 3 ⟨by norm_num, by norm_num⟩,
    forwardEquation_betaPDFReal 2 3 ⟨by norm_num, by norm_num⟩⟩

/-- The density relates to `wrightDensity` with halved rates. -/
example : betaPDFReal 2 2 (1 / 2) = wrightDensity 1 1 (1 / 2) / beta 2 2 := by
  have h := betaPDFReal_eq_wrightDensity 2 2 (x := 1 / 2) ⟨by norm_num, by norm_num⟩
  norm_num at h ⊢
  exact h

/-- Without mutation (`u₁ = u₂ = 0`) the post-mutation frequency is unchanged. -/
example (x : unitInterval) : (mutatedFreq 0 0 x : ℝ) = x := by
  simp [mutatedFreq]

/-- Boundary: an absent allele (`x = 0`) is reintroduced at frequency `u₁`. -/
example (u₁ u₂ : unitInterval) : (mutatedFreq u₁ u₂ 0 : ℝ) = u₁ := by
  simp [mutatedFreq]

/-- One generation with `M = 10` copies and symmetric rates: the drift vanishes at `x = 1/2`. -/
example {u : unitInterval} (hu : (u : ℝ) = 1 / (2 * (10 : ℕ))) (x : unitInterval)
    (hx : (x : ℝ) = 1 / 2) :
    (10 : ℕ) * (∫ k, (k : ℝ) / (10 : ℕ) ∂(binomial 10 (mutatedFreq u u x)) - x) = 0 := by
  rw [integral_binomial_mutatedFreq_drift (θ₁ := 1) (θ₂ := 1) (by norm_num) hu hu x, hx]
  norm_num

/-- Junk value outside the domain: for `θ₂ = 0` the normalizing constant `B(1, 0)` is `0`
(`Γ(0) = 0` in Mathlib), so `betaMeasure 1 0` is the zero measure and its "mean" is `0`, not the
formula's `θ₁ / (θ₁ + θ₂) = 1`. This is why the moment theorems assume `θ₁, θ₂ > 0`. -/
example : ∫ x, x ∂(betaMeasure 1 0) = 0 := by
  have hB : beta 1 0 = 0 := by simp [beta]
  have hpdf : betaPDF 1 0 = 0 := by
    funext x
    simp [betaPDF, betaPDFReal, hB]
  simp [betaMeasure, hpdf]

/-- One generation with `M = 2` copies, `θ₁ = 1`, `θ₂ = 1/2` (so `u₁ = 1/4`, `u₂ = 1/8`) and
`x = 1/2`: mutation moves the frequency to `p' = 9/16`, and the scaled second moment is
`p' (1 - p') + (θ₁ (1 - x) - θ₂ x) ^ 2 / (4M) = 63/256 + 1/128 = 65/256`. -/
example {u₁ u₂ x : unitInterval} (hu₁ : (u₁ : ℝ) = 1 / 4) (hu₂ : (u₂ : ℝ) = 1 / 8)
    (hx : (x : ℝ) = 1 / 2) :
    (2 : ℕ) * ∫ k, ((k : ℝ) / (2 : ℕ) - x) ^ 2 ∂(binomial 2 (mutatedFreq u₁ u₂ x)) =
      65 / 256 := by
  rw [integral_binomial_mutatedFreq_sq (θ₁ := 1) (θ₂ := 1 / 2) (by norm_num)
    (by rw [hu₁]; norm_num) (by rw [hu₂]; norm_num) x]
  simp only [mutatedFreq, hu₁, hu₂, hx]
  norm_num

/-- The same value by direct summation over `k = 0, 1, 2` with `p' = 9/16`. -/
example {u₁ u₂ x : unitInterval} (hu₁ : (u₁ : ℝ) = 1 / 4) (hu₂ : (u₂ : ℝ) = 1 / 8)
    (hx : (x : ℝ) = 1 / 2) :
    (2 : ℕ) * ∫ k, ((k : ℝ) / (2 : ℕ) - x) ^ 2 ∂(binomial 2 (mutatedFreq u₁ u₂ x)) =
      65 / 256 := by
  rw [integral_binomial, ← Nat.range_succ_eq_Iic]
  simp only [mutatedFreq, hu₁, hu₂, hx, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

#print axioms integral_mutationGenerator_betaMeasure
#print axioms integral_heterozygosity_betaMeasure
#print axioms integral_binomial_mutatedFreq_sq

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.Mutation
