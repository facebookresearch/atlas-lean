/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Data.Matrix.Mul

/-!
# Conditional case probabilities in matched sets

Given exactly one case in a matched set, the case probabilities are independent of the
intercept and invariant under a common additive shift of all subjects' exposure vectors.
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.ConditionalLogisticMatchedSetsWanted

/-- The probability that subject `j` of a matched set is the only case, when outcomes are
independent with `P(y_i = 1) = σ(α + β · x_i)`:
`σ(α + β · x_j) ∏_{i ≠ j} (1 - σ(α + β · x_i))`. Here `σ` is the logistic
function `Real.sigmoid`. -/
noncomputable def onlyCaseProb {M K : ℕ} (α : ℝ) (β : Fin K → ℝ) (x : Fin (M + 1) → Fin K → ℝ)
    (j : Fin (M + 1)) : ℝ :=
  Real.sigmoid (α + β ⬝ᵥ x j) * ∏ i ∈ Finset.univ.erase j, (1 - Real.sigmoid (α + β ⬝ᵥ x i))

/-- The conditional probability that subject `j` is the case, given exactly one case in the set. The
denominator is always positive (every factor lies in `(0, 1)`), so no division by zero occurs. -/
noncomputable def conditionalCaseProb {M K : ℕ} (α : ℝ) (β : Fin K → ℝ)
    (x : Fin (M + 1) → Fin K → ℝ) (j : Fin (M + 1)) : ℝ :=
  onlyCaseProb α β x j / ∑ i, onlyCaseProb α β x i

/-- **The conditional probability is free of the intercept** (Breslow and Day 1980, ch. 7). For
a matched set of `M + 1` subjects with exposures `x_i ∈ ℝ^K`, independent outcomes with
`P(y_i = 1) = σ(α + β · x_i)`, every intercept `α ∈ ℝ` and coefficient vector `β`, the
probability that subject `j` is the case given exactly one case is
`exp(β · x_j) / ∑_i exp(β · x_i)`.
Here `σ` is the logistic function `Real.sigmoid`.

Source: Breslow and Day (1980), p. 251. -/
public theorem conditionalCaseProb_eq {M K : ℕ} (α : ℝ) (β : Fin K → ℝ)
    (x : Fin (M + 1) → Fin K → ℝ) (j : Fin (M + 1)) :
    conditionalCaseProb α β x j = Real.exp (β ⬝ᵥ x j) / ∑ i, Real.exp (β ⬝ᵥ x i) := by
  -- `σ t = e^t (1 - σ t)`, so each `onlyCaseProb` is `e^(β · x_i)` times one positive constant.
  have hσ (t : ℝ) : Real.sigmoid t = Real.exp t * (1 - Real.sigmoid t) := by
    have h := Real.sigmoid_mul_rexp_neg (-t)
    rw [neg_neg, Real.sigmoid_neg] at h
    rw [mul_comm]
    exact h.symm
  set c := Real.exp α * ∏ k, (1 - Real.sigmoid (α + β ⬝ᵥ x k)) with hc
  have hc0 : 0 < c :=
    mul_pos (Real.exp_pos _) (Finset.prod_pos fun k _ => sub_pos.mpr (Real.sigmoid_lt_one _))
  have honly (i : Fin (M + 1)) : onlyCaseProb α β x i = Real.exp (β ⬝ᵥ x i) * c := by
    rw [onlyCaseProb, hσ (α + β ⬝ᵥ x i), mul_assoc,
      Finset.mul_prod_erase Finset.univ (fun k => 1 - Real.sigmoid (α + β ⬝ᵥ x k))
        (Finset.mem_univ i), Real.exp_add, hc]
    ring
  simp_rw [conditionalCaseProb, honly, ← Finset.sum_mul]
  exact mul_div_mul_right _ _ hc0.ne'

/-- **Matching variables drop out** (Breslow and Day 1980, p. 251). For a matched set of `M + 1`
subjects with exposures `x_i ∈ ℝ^K`, independent outcomes with `P(y_i = 1) = σ(α + β · x_i)`,
every intercept `α`, coefficient vector `β` and vector `z ∈ ℝ^K` common to the whole set, the
conditional probability that subject `j` is the case given exactly one case is unchanged when
every exposure `x_i` is replaced by `x_i + z`.
Here `σ` is the logistic function `Real.sigmoid`.

Source: Breslow and Day (1980), p. 251. -/
public theorem conditionalCaseProb_add_const {M K : ℕ} (α : ℝ) (β : Fin K → ℝ)
    (x : Fin (M + 1) → Fin K → ℝ) (z : Fin K → ℝ) (j : Fin (M + 1)) :
    conditionalCaseProb α β (fun i => x i + z) j = conditionalCaseProb α β x j := by
  simp_rw [conditionalCaseProb_eq, dotProduct_add, Real.exp_add, ← Finset.sum_mul]
  exact mul_div_mul_right _ _ (Real.exp_pos (β ⬝ᵥ z)).ne'

end WantedExt.Biology.StatisticalGenetics.ConditionalLogisticMatchedSetsWanted
