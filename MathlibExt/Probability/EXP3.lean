/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Field

/-!
# EXP3 loss estimator

The importance-weighted loss estimator used by EXP3 is
unbiased under the sampling distribution, and normalized
weights sum to one. Regret analysis is not included here.
-/

@[expose] public section

/-- EXP3 importance-weighted loss estimator (ML-34 core).
Arms are `Fin n`; `p` is the sampling distribution, `l`
the loss vector. When arm `j` is sampled, the estimate for
arm `i` is `l i / p i` if `j = i` and `0` otherwise. -/
noncomputable def lossEst {n : ℕ} (p l : Fin n → ℝ) (j i : Fin n) : ℝ :=
  if j = i then l i / p i else 0

/-- Unbiasedness: the `p`-expectation of the estimator for
arm `i` is the true loss `l i`. -/
theorem lossEst_expectation {n : ℕ} (p l : Fin n → ℝ)
    (i : Fin n) (hi : p i ≠ 0) :
    ∑ j, p j * lossEst p l j i = l i := by
  rw [Finset.sum_eq_single i]
  · unfold lossEst
    rw [ite_eq_left rfl]
    exact mul_div_cancel₀ _ hi
  · intro j _ hji
    simp only [lossEst, ite_eq_right hji, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon

/-- Weights normalized by their total give sampling
probabilities summing to one. -/
theorem exp3_probs_sum {n : ℕ} (w : Fin n → ℝ)
    (hw : (0:ℝ) < ∑ i, w i) :
    ∑ i, w i / (∑ j, w j) = 1 := by
  rw [← Finset.sum_div]
  exact div_self hw.ne'

end
