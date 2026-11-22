/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Leverage scores

Row leverage scores of a matrix with orthonormal columns
sum to the number of columns. Spectral sparsification is
not included here.
-/

@[expose] public section

/-- Leverage scores of a matrix with orthonormal columns
(ALG-55 core). For `A : Fin m → Fin n → ℝ` whose columns
are orthonormal, the leverage score of row `i` is
`∑ j, (A i j)^2`. -/
noncomputable def leverage {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (i : Fin m) : ℝ :=
  ∑ j, (A i j) ^ 2

/-- The leverage scores sum to the number of columns. -/
theorem leverage_sum {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (horth : ∀ j j', ∑ i, A i j * A i j' = if j = j' then 1 else 0) :
    ∑ i, leverage A i = n := by
  unfold leverage
  rw [Finset.sum_comm]
  have hdiag : ∀ j : Fin n, (∑ i, (A i j) ^ 2) = 1 := by
    intro j
    simpa [pow_two] using horth j j
  simp [hdiag]

end
