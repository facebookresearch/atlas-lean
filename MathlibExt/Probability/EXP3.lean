/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# EXP3 loss estimator

The importance-weighted loss estimator used by EXP3 is unbiased under the
sampling distribution (`lossEst_expectation`). Normalizing weights to total
mass one is `MathlibExt.Probability.FiniteProbability.sum_div_sum_eq_one`.
Regret analysis is not included here.

## References

* P. Auer, N. Cesa-Bianchi, Y. Freund and R. E. Schapire, *The nonstochastic
  multiarmed bandit problem*, SIAM J. Comput. 32 (2002).
* T. Lattimore and C. Szepesvári, *Bandit Algorithms*, Cambridge University
  Press, 2020, Chapter 11.
-/

@[expose] public section

namespace MathlibExt.Probability.EXP3

/-- EXP3 importance-weighted loss estimator. Arms are `Fin n`; `p` is the
sampling distribution and `l` the loss vector. When arm `j` is sampled, the
estimate for arm `i` is `l i / p i` if `j = i` and `0` otherwise. If
`p i = 0`, the `j = i` value is `0` by Lean's convention `x / 0 = 0`; EXP3
samples every arm with positive probability, and `lossEst_expectation`
assumes `p i ≠ 0`. -/
noncomputable def lossEst {n : ℕ} (p l : Fin n → ℝ) (j i : Fin n) : ℝ :=
  if j = i then l i / p i else 0

/-- Unbiasedness: for weights `p` with `p i ≠ 0`, the `p`-weighted sum of the
estimator for arm `i` is the true loss `l i`. When `p` is the sampling
distribution, this weighted sum is the estimator's expectation. -/
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

end MathlibExt.Probability.EXP3

end
