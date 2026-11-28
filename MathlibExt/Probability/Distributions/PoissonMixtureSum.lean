/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.PoissonMixture
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.MeasureTheory.Constructions.Pi

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Sums of independent mixed Poisson counts

Let `Nᵢ`, for `i` in a finite type `ι`, be counts with independent rates `Λᵢ ~ νᵢ`, and given the
rates let the `Nᵢ` be independent with `Nᵢ ~ Po(Λᵢ)`. Given the rates, the total `N = ∑ᵢ Nᵢ` is
Poisson with mean `∑ᵢ Λᵢ`, so `N` is mixed Poisson over the law of `∑ᵢ Λᵢ`, the image of the
product law `⊗ᵢ νᵢ` under `x ↦ ∑ᵢ xᵢ`. Its mass function is the convolution of the mixed Poisson
mass functions of the `Nᵢ`:

`P(N = k) = ∑_{j} ∏ᵢ pᵢ(jᵢ)`, over the `j : ι → ℕ` with `∑ᵢ jᵢ = k`,

where `pᵢ = poissonMixtureReal νᵢ`. The proof expands the Poisson mass of the total rate by the
multinomial theorem and integrates the products coordinatewise (Fubini).

## Main results

* `ProbabilityTheory.poissonMixtureReal_pi_map_sum`: the mixed Poisson mass function over the law
  of a sum of independent rates is the convolution of the mixed Poisson mass functions.

## References

* J. Grandell, *Mixed Poisson Processes*, Chapman & Hall (1997), ch. 2.
-/

@[expose] public section

open MeasureTheory Real Finset
open scoped Nat

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Poisson mass of a total, split over its summands: for real `xᵢ`,
`e^{-∑ xᵢ} (∑ xᵢ)ᵏ / k! = ∑_{j} ∏ᵢ e^{-xᵢ} xᵢ^{jᵢ} / jᵢ!` over the `j : ι → ℕ` with
`∑ᵢ jᵢ = k` (the multinomial theorem). -/
private lemma exp_neg_sum_mul_sum_pow_div (x : ι → ℝ) (k : ℕ) :
    exp (-∑ i, x i) * (∑ i, x i) ^ k / (k ! : ℝ) =
      ∑ j ∈ univ.piAntidiag k, ∏ i, exp (-x i) * x i ^ j i / ((j i)! : ℝ) := by
  rw [sum_pow_eq_sum_piAntidiag, mul_sum, sum_div]
  refine sum_congr rfl fun j hj => ?_
  have hk : ∑ i, j i = k := (mem_piAntidiag.1 hj).1
  have hm : (Nat.multinomial univ j : ℝ) * ∏ i, ((j i)! : ℝ) = k ! := by
    rw [← hk, mul_comm]
    exact_mod_cast Nat.multinomial_spec univ j
  have hP : ∏ i, ((j i)! : ℝ) ≠ 0 :=
    prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hM : (Nat.multinomial univ j : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.multinomial_pos _ _).ne'
  rw [prod_div_distrib, prod_mul_distrib, ← exp_sum, sum_neg_distrib, ← hm]
  field_simp

/-- A Poisson mass `r ↦ e^{-r} rⁿ / n!` is integrable for a finite measure concentrated on
`[0, ∞)`, where it lies in `[0, 1]`. -/
private lemma integrable_poisson_mass {ν : Measure ℝ} [IsFiniteMeasure ν]
    (h0 : ∀ᵐ r ∂ν, 0 ≤ r) (n : ℕ) :
    Integrable (fun r => exp (-r) * r ^ n / (n ! : ℝ)) ν := by
  refine Integrable.of_bound (by fun_prop) 1 (h0.mono fun r hr => ?_)
  have h := Real.pow_div_factorial_le_exp r hr n
  rw [Real.norm_of_nonneg (by positivity), mul_div_assoc]
  calc exp (-r) * (r ^ n / n !) ≤ exp (-r) * exp r := by gcongr
    _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]

/-- **Sums of independent mixed Poisson counts.** Let the counts `Nᵢ`, `i ∈ ι`, be independent
given independent rates `Λᵢ ~ νᵢ`, with `Nᵢ ~ Po(Λᵢ)`. Given the rates the total `∑ᵢ Nᵢ` is
`Po(∑ᵢ Λᵢ)`, so its law is the mixed Poisson law over the image of `⊗ᵢ νᵢ` under
`x ↦ ∑ᵢ xᵢ`. For finite measures `νᵢ` concentrated on `[0, ∞)`, its mass at `k` is the
convolution of the mixed Poisson masses, `∑_{j} ∏ᵢ pᵢ(jᵢ)` over the `j : ι → ℕ` with
`∑ᵢ jᵢ = k`, where `pᵢ = poissonMixtureReal νᵢ`. -/
theorem poissonMixtureReal_pi_map_sum {ν : ι → Measure ℝ} [∀ i, IsFiniteMeasure (ν i)]
    (h0 : ∀ i, ∀ᵐ r ∂ν i, 0 ≤ r) (k : ℕ) :
    poissonMixtureReal ((Measure.pi ν).map fun x => ∑ i, x i) k =
      ∑ j ∈ univ.piAntidiag k, ∏ i, poissonMixtureReal (ν i) (j i) := by
  have hmeas : Measurable fun x : ι → ℝ => ∑ i, x i := by fun_prop
  rw [poissonMixtureReal, integral_map hmeas.aemeasurable (by fun_prop)]
  simp_rw [exp_neg_sum_mul_sum_pow_div]
  rw [integral_finsetSum _ fun j _ =>
    Integrable.fintype_prod fun i => integrable_poisson_mass (h0 i) (j i)]
  refine sum_congr rfl fun j _ => ?_
  exact integral_fintype_prod_eq_prod (fun i r => exp (-r) * r ^ j i / ((j i)! : ℝ))

end ProbabilityTheory
