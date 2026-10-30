/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith

/-!
# Rate matrices of finite continuous-time Markov chains

A **rate matrix** (or `Q`-matrix) on a finite state space `ι` is a real square matrix whose
off-diagonal entries are nonnegative and whose rows sum to `0`. The entry `Q i j` (`i ≠ j`) is
the jump rate from `i` to `j`, and `-Q i i = ∑_{j ≠ i} Q i j` is the total rate of leaving `i`.
On a finite state space these are exactly Norris's `Q`-matrices.

The transition function `exp (t • Q)` of the chain is studied in
`MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Semigroup`.

## Main definitions

* `ProbabilityTheory.IsRateMatrix Q`: `Q` is a rate matrix.

## Main results

* `IsRateMatrix.diag_eq`: the diagonal entry is minus the sum of the off-diagonal entries.
* `IsRateMatrix.diag_nonpos`: the diagonal entries are nonpositive.
* `IsRateMatrix.mulVec_one`: `Q *ᵥ 1 = 0`.
* `IsRateMatrix.add_smul_one_nonneg`: **uniformization** — if `c ≥ -Q i i` for every `i`, then
  `Q + c • 1` has nonnegative entries.
* `IsRateMatrix.exists_add_smul_one_nonneg`: such a `c ≥ 0` exists.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §2.1.
* A. Jensen, *Markoff chains as an aid in the study of Markoff processes*, Skand.
  Aktuarietidskr. 36 (1953), 87–91 (uniformization).
-/

@[expose] public section

open Finset Matrix

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- A real square matrix `Q` is a **rate matrix** (a `Q`-matrix in Norris's terminology) if its
off-diagonal entries are nonnegative and each of its rows sums to `0` (Norris 1997, §2.1). -/
structure IsRateMatrix (Q : Matrix ι ι ℝ) : Prop where
  /-- The jump rates `Q i j`, `i ≠ j`, are nonnegative. -/
  nonneg_of_ne : ∀ ⦃i j : ι⦄, i ≠ j → 0 ≤ Q i j
  /-- Each row sums to `0`. -/
  sum_row : ∀ i, ∑ j, Q i j = 0

namespace IsRateMatrix

variable {Q : Matrix ι ι ℝ}

/-- The diagonal entry of a rate matrix is minus the total jump rate out of the state. -/
theorem diag_eq [DecidableEq ι] (hQ : IsRateMatrix Q) (i : ι) :
    Q i i = -∑ j ∈ univ.erase i, Q i j := by
  have h := hQ.sum_row i
  rw [← add_sum_erase _ _ (mem_univ i)] at h
  linarith

/-- The diagonal entries of a rate matrix are nonpositive. -/
theorem diag_nonpos (hQ : IsRateMatrix Q) (i : ι) : Q i i ≤ 0 := by
  classical
  rw [hQ.diag_eq i, neg_nonpos]
  exact sum_nonneg fun j hj => hQ.nonneg_of_ne (ne_of_mem_erase hj).symm

/-- A rate matrix annihilates the constant vector `1`. -/
theorem mulVec_one (hQ : IsRateMatrix Q) : Q *ᵥ 1 = 0 := by
  ext i
  simp [mulVec, dotProduct, hQ.sum_row i]

/-- **Uniformization**: if `c` bounds every exit rate `-Q i i`, then `Q + c • 1` has
nonnegative entries (Jensen 1953). -/
theorem add_smul_one_nonneg [DecidableEq ι] (hQ : IsRateMatrix Q) {c : ℝ}
    (hc : ∀ i, -Q i i ≤ c) (i j : ι) :
    0 ≤ (Q + c • (1 : Matrix ι ι ℝ)) i j := by
  by_cases h : i = j
  · subst h
    have := hc i
    simp only [Matrix.add_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
    linarith
  · simpa [one_apply_ne h] using hQ.nonneg_of_ne h

/-- Every rate matrix admits a uniformization constant `c ≥ 0`. -/
theorem exists_add_smul_one_nonneg [DecidableEq ι] (hQ : IsRateMatrix Q) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ i j, 0 ≤ (Q + c • (1 : Matrix ι ι ℝ)) i j := by
  refine ⟨∑ k, -Q k k, sum_nonneg fun k _ => neg_nonneg.mpr (hQ.diag_nonpos k),
    hQ.add_smul_one_nonneg fun i => ?_⟩
  exact single_le_sum (f := fun k => -Q k k) (fun k _ => neg_nonneg.mpr (hQ.diag_nonpos k))
    (mem_univ i)

end IsRateMatrix

end ProbabilityTheory
