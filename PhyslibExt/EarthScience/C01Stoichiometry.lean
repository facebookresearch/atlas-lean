/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add

import Mathlib.Analysis.Calculus.Deriv.Mul
/-!
# Stoichiometric conservation from a left-null vector

For a concentration trajectory obeying `c' = S * v(c)` with stoichiometric
matrix `S`, every left-null vector `l` of `S` gives a conserved linear
combination `∑ i, l i * c i`.

## i. Overview

Species are indexed by `Fin n`, reactions by `Fin m`. Hypothesis `hode`
says each concentration obeys `c_i'(t) = ∑ j, S i j * rate_j` at time `t`,
and `hnull` says `l` is a left-null vector of `S`: for every reaction `j`,
`∑ i, l i * S i j = 0`. Summing the balance laws weighted by `l` and
swapping the sums, the derivative of `∑ i, l i * c t i` is `0`: internal
stoichiometry cancels and only the null-space structure matters.

This is the ODE form of stoichiometric conservation. It is distinct from
the algebraic extent conservation in `PhyslibExt.Chemistry.Stoichiometry.Balance`
(open PR #1148), which conserves balance coordinates under reaction
extents and involves no derivatives.

## ii. Key results

- `EarthScience.stoichiometric_leftNull_conserved`: the `l`-weighted total
  concentration has derivative `0`.

## iii. References

- `HasDerivAt.fun_sum` in `Mathlib/Analysis/Calculus/Deriv/Add.lean`.
- `Finset.sum_comm` for swapping the species/reaction sums.
-/

@[expose] public section

namespace EarthScience

/-- Stoichiometric conservation: for `c' = S * v(c)` (species `i`,
reactions `j`, `S i j` the stoichiometric coefficient), every left-null
vector `l` of `S` gives a conserved linear combination `∑ i, l i * c t i`,
whose derivative is `0`. -/
theorem stoichiometric_leftNull_conserved {n m : ℕ}
    (S : Fin n → Fin m → ℝ) (l : Fin n → ℝ)
    (c : ℝ → Fin n → ℝ) (rate : (Fin n → ℝ) → Fin m → ℝ) (t : ℝ)
    (hnull : ∀ j, ∑ i, l i * S i j = 0)
    (hode : ∀ i, HasDerivAt (fun t => c t i) (∑ j, S i j * rate (c t) j) t) :
    HasDerivAt (fun t => ∑ i, l i * c t i) 0 t := by
  have hsum : HasDerivAt (fun t => ∑ i, l i * c t i)
      (∑ i, l i * (∑ j, S i j * rate (c t) j)) t :=
    HasDerivAt.fun_sum (fun i _ => (hode i).const_mul (l i))
  have hzero : (∑ i, l i * (∑ j, S i j * rate (c t) j)) = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero ?_
    intro j _
    have hrw : (∑ i, l i * (S i j * rate (c t) j))
        = (∑ i, l i * S i j) * rate (c t) j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hrw, hnull j, zero_mul]
  rw [hzero] at hsum
  exact hsum

end EarthScience
