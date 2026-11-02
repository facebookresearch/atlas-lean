/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Probability.Distributions.NegativeBinomialSplitting

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Moments of the beta-binomial distribution

The beta-binomial law with `n` trials and shape parameters `α, β > 0` is the binomial law whose
success probability is `Beta(α, β)`-distributed. Its mass function is

`P(k) = C(n, k) B(k + α, n - k + β) / B(α, β) = C(n, k) α⁽ᵏ⁾ β⁽ⁿ⁻ᵏ⁾ / (α + β)⁽ⁿ⁾`,

with rising factorials `x⁽ᵐ⁾ = x (x + 1) ⋯ (x + m - 1)` (`ascPochhammer`). In the
parametrization of Dolzhenko and Smith (2014), used for overdispersed methylation counts,
`π = α / (α + β)` and `γ = 1 / (α + β + 1)`, and

`E M = n π`, `Var M = n π (1 - π) (1 + (n - 1) γ)`.

The mass function, the Chu–Vandermonde identity
(`ascPochhammer_eval_add_eq_sum`) and normalization (`sum_betaBinomialPMF`) are reused from
`MathlibExt.Probability.Distributions.NegativeBinomialSplitting`; this file adds only the
moment results for `betaBinomialPMF`.

## Main results

* `sum_mul_betaBinomialPMF`: `E M = n π`.
* `sum_mul_sub_one_betaBinomialPMF`: `E[M (M - 1)] = n (n - 1) α (α + 1) / ((α + β) (α + β + 1))`.
* `variance_betaBinomial`: `Var M = n π (1 - π) (1 + (n - 1) γ)`.

The representation as a Beta mixture of binomial laws is not formalized here.

## References

* E. Dolzhenko and A. D. Smith, *Using beta-binomial regression for high-precision differential
  methylation analysis in multifactor whole-genome bisulfite sequencing experiments*,
  BMC Bioinformatics 15 (2014), 215.
* N. L. Johnson, A. W. Kemp and S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley
  (2005), ch. 6.
-/

@[expose] public section

open Finset Polynomial

namespace ProbabilityTheory

/-- **Shift identity.** Weighting by the count `k` lowers the number of trials and raises `α`:
`∑_{k ≤ m + 1} k g(k) C(m + 1, k) α⁽ᵏ⁾ β⁽ᵐ⁺¹⁻ᵏ⁾ =
(m + 1) α ∑_{j ≤ m} g(j + 1) C(m, j) (α + 1)⁽ʲ⁾ β⁽ᵐ⁻ʲ⁾`. -/
private lemma sum_mul_choose_ascPochhammer_succ (m : ℕ) (α β : ℝ) (g : ℕ → ℝ) :
    ∑ k ∈ range (m + 2), (k : ℝ) * g k *
        ((m + 1).choose k * (ascPochhammer ℝ k).eval α * (ascPochhammer ℝ (m + 1 - k)).eval β) =
      (m + 1) * α * ∑ j ∈ range (m + 1), g (j + 1) *
        (m.choose j * (ascPochhammer ℝ j).eval (α + 1) * (ascPochhammer ℝ (m - j)).eval β) := by
  rw [sum_range_succ', mul_sum]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  refine sum_congr rfl fun j _ => ?_
  have hc : ((j + 1 : ℕ) : ℝ) * ((m + 1).choose (j + 1) : ℝ) = (m + 1) * (m.choose j : ℝ) := by
    exact_mod_cast (Nat.mul_comm _ _).trans (Nat.add_one_mul_choose_eq m j).symm
  rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add, eval_X, eval_one,
    Nat.add_sub_add_right]
  linear_combination (g (j + 1) * α * (ascPochhammer ℝ j).eval (α + 1) *
    (ascPochhammer ℝ (m - j)).eval β) * hc

/-- `(α + β)⁽ⁿ⁾ > 0` for `α, β > 0`. -/
private lemma ascPochhammer_add_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    0 < (ascPochhammer ℝ n).eval (α + β) :=
  ascPochhammer_pos n _ (add_pos hα hβ)

/-- The sum of `f(k) P(k)` over `k ≤ n`, with the denominator pulled out. -/
private lemma sum_mul_betaBinomialPMF_eq (n : ℕ) (α β : ℝ) (f : ℕ → ℝ) :
    ∑ k ∈ range (n + 1), f k * betaBinomialPMF n α β k =
      (∑ k ∈ range (n + 1), f k * (n.choose k * (ascPochhammer ℝ k).eval α *
        (ascPochhammer ℝ (n - k)).eval β)) / (ascPochhammer ℝ n).eval (α + β) := by
  rw [sum_div]
  refine sum_congr rfl fun k _ => ?_
  rw [betaBinomialPMF, mul_div_assoc]

/-- **Mean.** For `α, β > 0`, `E M = n α / (α + β) = n π`. -/
theorem sum_mul_betaBinomialPMF {n : ℕ} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∑ k ∈ range (n + 1), (k : ℝ) * betaBinomialPMF n α β k = n * α / (α + β) := by
  rw [sum_mul_betaBinomialPMF_eq]
  rcases n with _ | m
  · simp
  · have h := sum_mul_choose_ascPochhammer_succ m α β (fun _ => 1)
    simp only [mul_one, one_mul] at h
    rw [h, ← ascPochhammer_eval_add_eq_sum, ascPochhammer_succ_left, eval_mul, eval_X,
      eval_comp, eval_add, eval_X, eval_one, show α + 1 + β = α + β + 1 by ring]
    have h1 := ascPochhammer_pos m (α + β + 1) (by linarith)
    have h2 : α + β ≠ 0 := by linarith
    push_cast
    field_simp

/-- **Second factorial moment.** For `α, β > 0`,
`E[M (M - 1)] = n (n - 1) α (α + 1) / ((α + β) (α + β + 1))`. -/
theorem sum_mul_sub_one_betaBinomialPMF {n : ℕ} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∑ k ∈ range (n + 1), (k : ℝ) * ((k : ℝ) - 1) * betaBinomialPMF n α β k =
      n * (n - 1) * α * (α + 1) / ((α + β) * (α + β + 1)) := by
  rw [sum_mul_betaBinomialPMF_eq]
  rcases n with _ | m
  · simp
  have h := sum_mul_choose_ascPochhammer_succ m α β (fun k => (k : ℝ) - 1)
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at h
  simp only [mul_assoc] at h ⊢
  rw [h]
  rcases m with _ | l
  · simp
  have h' := sum_mul_choose_ascPochhammer_succ l (α + 1) β (fun _ => 1)
  simp only [mul_one, one_mul, mul_assoc] at h'
  have hV := (ascPochhammer_eval_add_eq_sum (α + 1 + 1) β l).symm
  simp only [mul_assoc] at hV
  rw [h', hV, ascPochhammer_succ_left, eval_mul, eval_X,
    eval_comp, eval_add, eval_X, eval_one, ascPochhammer_succ_left, eval_mul, eval_X,
    eval_comp, eval_add, eval_X, eval_one, show α + 1 + 1 + β = α + β + 1 + 1 by ring]
  have h1 := ascPochhammer_pos l (α + β + 1 + 1) (by linarith)
  have h2 : α + β ≠ 0 := by linarith
  have h3 : α + β + 1 ≠ 0 := by linarith
  push_cast
  field_simp
  ring

/-- **Variance** (Dolzhenko–Smith parametrization). For `α, β > 0`, with `π = α / (α + β)` and
`γ = 1 / (α + β + 1)`, `Var M = E M² - (E M)² = n π (1 - π) (1 + (n - 1) γ)`. -/
theorem variance_betaBinomial {n : ℕ} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∑ k ∈ range (n + 1), (k : ℝ) ^ 2 * betaBinomialPMF n α β k -
        (∑ k ∈ range (n + 1), (k : ℝ) * betaBinomialPMF n α β k) ^ 2 =
      n * (α / (α + β)) * (1 - α / (α + β)) * (1 + (n - 1) * (1 / (α + β + 1))) := by
  have hsq : ∑ k ∈ range (n + 1), (k : ℝ) ^ 2 * betaBinomialPMF n α β k =
      ∑ k ∈ range (n + 1), (k : ℝ) * ((k : ℝ) - 1) * betaBinomialPMF n α β k +
        ∑ k ∈ range (n + 1), (k : ℝ) * betaBinomialPMF n α β k := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [hsq, sum_mul_sub_one_betaBinomialPMF hα hβ, sum_mul_betaBinomialPMF hα hβ]
  have h2 : α + β ≠ 0 := by linarith
  have h3 : α + β + 1 ≠ 0 := by linarith
  field_simp
  ring

end ProbabilityTheory
