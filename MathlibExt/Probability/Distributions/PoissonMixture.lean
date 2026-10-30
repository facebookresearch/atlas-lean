/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Mixed Poisson distributions

A count `N` is *mixed Poisson* with mixing law `ν` when, given a random rate `Λ ~ ν` on
`[0, ∞)`, `N` is Poisson with mean `Λ`. Its mass function is

`p(k) = ∫ e^{-λ} λ^k / k! dν(λ)`.

Mixed Poisson laws model overdispersed counts such as molecule counts in single-cell RNA
sequencing, where `Λ` is the cell-to-cell variation in expression.

## Main definitions

* `ProbabilityTheory.poissonMixtureReal ν k`: the mixed Poisson mass function `p(k)`.

## Main results

For a probability measure `ν` on `ℝ` concentrated on `[0, ∞)`:

* `poissonMixtureReal_dirac`: with no rate variation the law is Poisson.
* `hasSum_poissonMixtureReal`: normalization `∑ₖ p(k) = 1`.
* `exp_neg_integral_le_poissonMixtureReal_zero`: the zero class is inflated relative to the
  Poisson law with the same mean, `P(N = 0) = E e^{-Λ} ≥ e^{-E Λ}` (Jensen).
* `hasSum_mul_poissonMixtureReal`: `E N = E Λ`.
* `hasSum_mul_sub_one_poissonMixtureReal`, `hasSum_sq_poissonMixtureReal`:
  `E[N (N - 1)] = E Λ²` and `E N² = E Λ² + E Λ`.
* `variance_poissonMixture`: `Var N = E Λ + Var Λ`.
* `cv_sq_poissonMixture`: `CV²(N) = 1 / E Λ + CV²(Λ)`, where `CV² = Var / mean²`.

## References

* V. Svensson, *Droplet scRNA-seq is not zero-inflated*, Nat. Biotechnol. 38 (2020), 147–150.
* J. Grandell, *Mixed Poisson Processes*, Chapman & Hall (1997), ch. 2.
* P. Brennecke et al., *Accounting for technical noise in single-cell RNA-seq experiments*,
  Nat. Methods 10 (2013), 1093–1095.
-/

@[expose] public section

open MeasureTheory Real
open scoped Nat

namespace ProbabilityTheory

variable {ν : Measure ℝ}

/-- The Poisson masses with mean `r` sum to one (for every real `r`). -/
private lemma hasSum_poisson (r : ℝ) : HasSum (fun k : ℕ => exp (-r) * r ^ k / (k ! : ℝ)) 1 := by
  convert (NormedSpace.expSeries_div_hasSum_exp r).mul_left (exp (-r)) using 1
  · simp_rw [mul_div_assoc]
  · simp [← exp_eq_exp_ℝ, ← exp_add]

/-- The Poisson law with mean `r` has mean `r`. -/
private lemma hasSum_mul_poisson (r : ℝ) :
    HasSum (fun k : ℕ => (k : ℝ) * (exp (-r) * r ^ k / (k ! : ℝ))) r := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
  have h := (hasSum_poisson r).mul_left r
  rw [mul_one] at h
  convert h using 1
  funext k
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The Poisson law with mean `r` has second factorial moment `r²`. -/
private lemma hasSum_mul_sub_one_poisson (r : ℝ) :
    HasSum (fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * (exp (-r) * r ^ k / (k ! : ℝ))) (r ^ 2) := by
  rw [← hasSum_nat_add_iff' 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    zero_mul, sub_self, mul_zero, zero_add, sub_zero]
  have h := (hasSum_poisson r).mul_left (r ^ 2)
  rw [mul_one] at h
  convert h using 1
  funext k
  rw [Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- Termwise integration of a nonnegative series with integrable sum. -/
private lemma hasSum_integral_of_nonneg {F : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hF_meas : ∀ k, Continuous (F k)) (hF0 : ∀ k, ∀ᵐ r ∂ν, 0 ≤ F k r)
    (hsum : ∀ᵐ r ∂ν, HasSum (fun k => F k r) (g r)) (hg : Integrable g ν) :
    HasSum (fun k => ∫ r, F k r ∂ν) (∫ r, g r ∂ν) :=
  hasSum_integral_of_dominated_convergence F (fun k => (hF_meas k).aestronglyMeasurable)
    (fun k => (hF0 k).mono fun _ hr => (Real.norm_of_nonneg hr).le)
    (hsum.mono fun _ hr => hr.summable)
    (hg.congr (hsum.mono fun _ hr => hr.tsum_eq.symm)) hsum

/-- The mixed Poisson mass function `p(k) = ∫ e^{-λ} λ^k / k! dν(λ)` for a mixing law `ν` of the
rate. It is a probability mass function when `ν` is a probability measure concentrated on
`[0, ∞)`, which the theorems below assume; for such `ν` the integrand lies in `[0, 1]`, so the
integral is never a junk value. -/
noncomputable def poissonMixtureReal (ν : Measure ℝ) (k : ℕ) : ℝ :=
  ∫ r, exp (-r) * r ^ k / (k ! : ℝ) ∂ν

/-- The zero class of a mixed Poisson law is `E e^{-Λ}`. -/
theorem poissonMixtureReal_zero (ν : Measure ℝ) :
    poissonMixtureReal ν 0 = ∫ r, exp (-r) ∂ν := by
  simp [poissonMixtureReal]

/-- The mixed Poisson mass function is nonnegative when `ν` is concentrated on `[0, ∞)`. -/
theorem poissonMixtureReal_nonneg (h0 : ∀ᵐ r ∂ν, 0 ≤ r) (k : ℕ) :
    0 ≤ poissonMixtureReal ν k :=
  integral_nonneg_of_ae (h0.mono fun r hr => by positivity)

/-- The Poisson mixture over a point mass `δ_m` is the Poisson law with mean `m`. -/
theorem poissonMixtureReal_dirac (m : ℝ) (k : ℕ) :
    poissonMixtureReal (Measure.dirac m) k = exp (-m) * m ^ k / k ! := by
  simp [poissonMixtureReal]

/-- **Normalization.** For a probability measure `ν` concentrated on `[0, ∞)`, the mixed
Poisson masses sum to one. -/
theorem hasSum_poissonMixtureReal [IsProbabilityMeasure ν] (h0 : ∀ᵐ r ∂ν, 0 ≤ r) :
    HasSum (poissonMixtureReal ν) 1 := by
  have h := hasSum_integral_of_nonneg (ν := ν) (F := fun k r => exp (-r) * r ^ k / (k ! : ℝ))
    (g := fun _ => 1) (fun k => by fun_prop)
    (fun k => h0.mono fun r hr => by positivity) (ae_of_all _ hasSum_poisson)
    (integrable_const _)
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
  exact h

/-- **Zero inflation by mixing** (Jensen's inequality for `λ ↦ e^{-λ}`). For a probability
measure `ν` with integrable rate, `P(N = 0) = E e^{-Λ} ≥ e^{-E Λ}`, the zero class of the Poisson
law with the same mean. -/
theorem exp_neg_integral_le_poissonMixtureReal_zero [IsProbabilityMeasure ν]
    (h0 : ∀ᵐ r ∂ν, 0 ≤ r) (hint : Integrable id ν) :
    exp (-∫ r, r ∂ν) ≤ poissonMixtureReal ν 0 := by
  set m := ∫ r, r ∂ν
  have hexp : Integrable (fun r => exp (-r)) ν :=
    (integrable_const (1 : ℝ)).mono' (by fun_prop) (h0.mono fun r hr => by
      rw [Real.norm_of_nonneg (exp_pos _).le]
      exact exp_le_one_iff.2 (by linarith))
  have h1 : Integrable (fun r => m - r) ν := (integrable_const m).sub hint
  have h2 : Integrable (fun r => m - r + 1) ν := h1.add (integrable_const 1)
  have htan : Integrable (fun r => exp (-m) * (m - r + 1)) ν := h2.const_mul _
  have hle : ∫ r, exp (-m) * (m - r + 1) ∂ν ≤ ∫ r, exp (-r) ∂ν := by
    refine integral_mono htan hexp fun r => ?_
    have h := add_one_le_exp (m - r)
    calc exp (-m) * (m - r + 1) ≤ exp (-m) * exp (m - r) :=
          mul_le_mul_of_nonneg_left h (exp_pos _).le
      _ = exp (-r) := by rw [← exp_add]; ring_nf
  rw [poissonMixtureReal_zero]
  refine le_trans (le_of_eq ?_) hle
  rw [integral_const_mul, integral_add h1 (integrable_const 1),
    integral_sub (f := fun _ => m) (g := fun r => r) (integrable_const m) hint]
  simp [m]

/-- **Mean.** For a mixing measure `ν` on `[0, ∞)` with integrable rate, `E N = E Λ`
(finiteness of `ν` is not needed for this identity). -/
theorem hasSum_mul_poissonMixtureReal (h0 : ∀ᵐ r ∂ν, 0 ≤ r)
    (hint : Integrable id ν) :
    HasSum (fun k : ℕ => (k : ℝ) * poissonMixtureReal ν k) (∫ r, r ∂ν) := by
  have h := hasSum_integral_of_nonneg (ν := ν)
    (F := fun k r => (k : ℝ) * (exp (-r) * r ^ k / (k ! : ℝ))) (g := fun r => r)
    (fun k => by fun_prop) (fun k => h0.mono fun r hr => by positivity)
    (ae_of_all _ hasSum_mul_poisson) hint
  simpa only [poissonMixtureReal, integral_const_mul] using h

/-- **Second factorial moment.** For a mixing measure `ν` on `[0, ∞)` with square-integrable
rate, `E[N (N - 1)] = E Λ²` (finiteness of `ν` is not needed for this identity). -/
theorem hasSum_mul_sub_one_poissonMixtureReal (h0 : ∀ᵐ r ∂ν, 0 ≤ r)
    (hint₂ : Integrable (fun r => r ^ 2) ν) :
    HasSum (fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * poissonMixtureReal ν k) (∫ r, r ^ 2 ∂ν) := by
  have hk : ∀ k : ℕ, 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := fun k => by
    rcases k with _ | k
    · simp
    · push_cast
      nlinarith
  have h := hasSum_integral_of_nonneg (ν := ν)
    (F := fun k r => (k : ℝ) * ((k : ℝ) - 1) * (exp (-r) * r ^ k / (k ! : ℝ)))
    (g := fun r => r ^ 2) (fun k => by fun_prop)
    (fun k => h0.mono fun r hr => mul_nonneg (hk k) (by positivity))
    (ae_of_all _ hasSum_mul_sub_one_poisson) hint₂
  simpa only [poissonMixtureReal, integral_const_mul] using h

/-- **Second moment.** For a finite mixing measure `ν` on `[0, ∞)` with square-integrable rate,
`E N² = E Λ² + E Λ`. -/
theorem hasSum_sq_poissonMixtureReal [IsFiniteMeasure ν] (h0 : ∀ᵐ r ∂ν, 0 ≤ r)
    (hint₂ : Integrable (fun r => r ^ 2) ν) :
    HasSum (fun k : ℕ => (k : ℝ) ^ 2 * poissonMixtureReal ν k)
      (∫ r, r ^ 2 ∂ν + ∫ r, r ∂ν) := by
  have hint : Integrable id ν :=
    ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 hint₂).integrable one_le_two
  convert (hasSum_mul_sub_one_poissonMixtureReal h0 hint₂).add
    (hasSum_mul_poissonMixtureReal h0 hint) using 1
  funext k
  ring

/-- **Variance decomposition.** For a probability measure `ν` on `[0, ∞)` with square-integrable
rate, `Var N = E N² - (E N)² = E Λ + Var Λ`: Poisson noise plus the variance of the rate. -/
theorem variance_poissonMixture [IsProbabilityMeasure ν] (h0 : ∀ᵐ r ∂ν, 0 ≤ r)
    (hmem : MemLp id 2 ν) :
    ∑' k : ℕ, (k : ℝ) ^ 2 * poissonMixtureReal ν k -
        (∑' k : ℕ, (k : ℝ) * poissonMixtureReal ν k) ^ 2 =
      ∫ r, r ∂ν + Var[id; ν] := by
  have hint₂ : Integrable (fun r => r ^ 2) ν := hmem.integrable_sq
  rw [(hasSum_sq_poissonMixtureReal h0 hint₂).tsum_eq,
    (hasSum_mul_poissonMixtureReal h0 (hmem.integrable one_le_two)).tsum_eq,
    variance_eq_sub hmem]
  simp only [id_eq, Pi.pow_apply]
  ring

/-- **Squared coefficient of variation** (Brennecke et al. 2013; Svensson 2020). For a
probability measure `ν` on `[0, ∞)` with square-integrable rate and `E Λ > 0`,
`CV²(N) = Var N / (E N)² = 1 / E Λ + Var Λ / (E Λ)² = 1 / E Λ + CV²(Λ)`. -/
theorem cv_sq_poissonMixture [IsProbabilityMeasure ν] (h0 : ∀ᵐ r ∂ν, 0 ≤ r)
    (hmem : MemLp id 2 ν) (hpos : 0 < ∫ r, r ∂ν) :
    (∑' k : ℕ, (k : ℝ) ^ 2 * poissonMixtureReal ν k -
        (∑' k : ℕ, (k : ℝ) * poissonMixtureReal ν k) ^ 2) /
        (∑' k : ℕ, (k : ℝ) * poissonMixtureReal ν k) ^ 2 =
      1 / ∫ r, r ∂ν + Var[id; ν] / (∫ r, r ∂ν) ^ 2 := by
  rw [variance_poissonMixture h0 hmem,
    (hasSum_mul_poissonMixtureReal h0 (hmem.integrable one_le_two)).tsum_eq]
  field_simp

end ProbabilityTheory
