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

## Main definitions

* `ProbabilityTheory.betaBinomialReal n α β k`: the beta-binomial mass function.

## Main results

* `sum_ascPochhammer_mul_ascPochhammer`: the Chu–Vandermonde identity
  `∑ₖ C(n, k) α⁽ᵏ⁾ β⁽ⁿ⁻ᵏ⁾ = (α + β)⁽ⁿ⁾`.
* `sum_betaBinomialReal`: normalization.
* `sum_mul_betaBinomialReal`: `E M = n π`.
* `sum_mul_sub_one_betaBinomialReal`: `E[M (M - 1)] = n (n - 1) α (α + 1) / ((α + β) (α + β + 1))`.
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

/-- The beta-binomial mass function `C(n, k) α⁽ᵏ⁾ β⁽ⁿ⁻ᵏ⁾ / (α + β)⁽ⁿ⁾` for `k ≤ n` (and `0` for
`k > n`), with rising factorials `x⁽ᵐ⁾`. The parameter domain is `α, β > 0`; there the
denominator is positive. -/
noncomputable def betaBinomialReal (n : ℕ) (α β : ℝ) (k : ℕ) : ℝ :=
  if k ≤ n then
    n.choose k * (ascPochhammer ℝ k).eval α * (ascPochhammer ℝ (n - k)).eval β /
      (ascPochhammer ℝ n).eval (α + β)
  else 0

/-- The beta-binomial mass function is nonnegative for `α, β > 0`. -/
theorem betaBinomialReal_nonneg {n : ℕ} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (k : ℕ) :
    0 ≤ betaBinomialReal n α β k := by
  unfold betaBinomialReal
  split_ifs
  · have h1 := ascPochhammer_pos k α hα
    have h2 := ascPochhammer_pos (n - k) β hβ
    have h3 := ascPochhammer_pos n (α + β) (add_pos hα hβ)
    positivity
  · exact le_rfl

/-- Chu–Vandermonde over the antidiagonal: `(α + β)⁽ⁿ⁾ = ∑_{i + j = n} C(n, i) α⁽ⁱ⁾ β⁽ʲ⁾`. -/
private lemma ascPochhammer_eval_add_antidiagonal (n : ℕ) (α β : ℝ) :
    (ascPochhammer ℝ n).eval (α + β) = ∑ ij ∈ antidiagonal n,
      (n.choose ij.1 : ℝ) * ((ascPochhammer ℝ ij.1).eval α * (ascPochhammer ℝ ij.2).eval β) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_mul
      (fun i j => (ascPochhammer ℝ i).eval α * (ascPochhammer ℝ j).eval β),
      ascPochhammer_succ_eval, ih, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun ij hij => ?_
    have hij' : ij.1 + ij.2 = n := mem_antidiagonal.1 hij
    rw [Nat.choose_symm_of_eq_add hij'.symm, ascPochhammer_succ_eval, ascPochhammer_succ_eval]
    rw [← hij']
    push_cast
    ring

/-- **Chu–Vandermonde identity for rising factorials.**
`∑ₖ C(n, k) α⁽ᵏ⁾ β⁽ⁿ⁻ᵏ⁾ = (α + β)⁽ⁿ⁾` for all real `α, β`. -/
theorem sum_ascPochhammer_mul_ascPochhammer (n : ℕ) (α β : ℝ) :
    ∑ k ∈ range (n + 1),
        (n.choose k : ℝ) * (ascPochhammer ℝ k).eval α * (ascPochhammer ℝ (n - k)).eval β =
      (ascPochhammer ℝ n).eval (α + β) := by
  rw [ascPochhammer_eval_add_antidiagonal, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (n.choose i : ℝ) * ((ascPochhammer ℝ i).eval α * (ascPochhammer ℝ j).eval β))]
  refine sum_congr rfl fun k _ => ?_
  ring

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
private lemma sum_mul_betaBinomialReal_eq (n : ℕ) (α β : ℝ) (f : ℕ → ℝ) :
    ∑ k ∈ range (n + 1), f k * betaBinomialReal n α β k =
      (∑ k ∈ range (n + 1), f k * (n.choose k * (ascPochhammer ℝ k).eval α *
        (ascPochhammer ℝ (n - k)).eval β)) / (ascPochhammer ℝ n).eval (α + β) := by
  rw [sum_div]
  refine sum_congr rfl fun k hk => ?_
  rw [betaBinomialReal, ite_eq_left (Nat.lt_succ_iff.1 (mem_range.1 hk))]
  ring

/-- **Normalization.** For `α, β > 0` the beta-binomial masses sum to one. -/
theorem sum_betaBinomialReal {n : ℕ} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∑ k ∈ range (n + 1), betaBinomialReal n α β k = 1 := by
  have h := sum_mul_betaBinomialReal_eq n α β (fun _ => 1)
  simp only [one_mul] at h
  rw [h, sum_ascPochhammer_mul_ascPochhammer, div_self (ascPochhammer_add_pos hα hβ n).ne']

/-- **Mean.** For `α, β > 0`, `E M = n α / (α + β) = n π`. -/
theorem sum_mul_betaBinomialReal {n : ℕ} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∑ k ∈ range (n + 1), (k : ℝ) * betaBinomialReal n α β k = n * α / (α + β) := by
  rw [sum_mul_betaBinomialReal_eq]
  rcases n with _ | m
  · simp
  · have h := sum_mul_choose_ascPochhammer_succ m α β (fun _ => 1)
    simp only [mul_one, one_mul] at h
    rw [h, sum_ascPochhammer_mul_ascPochhammer, ascPochhammer_succ_left, eval_mul, eval_X,
      eval_comp, eval_add, eval_X, eval_one, show α + 1 + β = α + β + 1 by ring]
    have h1 := ascPochhammer_pos m (α + β + 1) (by linarith)
    have h2 : α + β ≠ 0 := by linarith
    push_cast
    field_simp

/-- **Second factorial moment.** For `α, β > 0`,
`E[M (M - 1)] = n (n - 1) α (α + 1) / ((α + β) (α + β + 1))`. -/
theorem sum_mul_sub_one_betaBinomialReal {n : ℕ} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∑ k ∈ range (n + 1), (k : ℝ) * ((k : ℝ) - 1) * betaBinomialReal n α β k =
      n * (n - 1) * α * (α + 1) / ((α + β) * (α + β + 1)) := by
  rw [sum_mul_betaBinomialReal_eq]
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
  have hV := sum_ascPochhammer_mul_ascPochhammer l (α + 1 + 1) β
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
    ∑ k ∈ range (n + 1), (k : ℝ) ^ 2 * betaBinomialReal n α β k -
        (∑ k ∈ range (n + 1), (k : ℝ) * betaBinomialReal n α β k) ^ 2 =
      n * (α / (α + β)) * (1 - α / (α + β)) * (1 + (n - 1) * (1 / (α + β + 1))) := by
  have hsq : ∑ k ∈ range (n + 1), (k : ℝ) ^ 2 * betaBinomialReal n α β k =
      ∑ k ∈ range (n + 1), (k : ℝ) * ((k : ℝ) - 1) * betaBinomialReal n α β k +
        ∑ k ∈ range (n + 1), (k : ℝ) * betaBinomialReal n α β k := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [hsq, sum_mul_sub_one_betaBinomialReal hα hβ, sum_mul_betaBinomialReal hα hβ]
  have h2 : α + β ≠ 0 := by linarith
  have h3 : α + β + 1 ≠ 0 := by linarith
  field_simp
  ring

end ProbabilityTheory
