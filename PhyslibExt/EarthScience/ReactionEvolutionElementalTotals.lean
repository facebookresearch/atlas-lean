/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
/-!
# Reaction evolution preserves conserved elemental totals

If `l` is a left-null vector of the stoichiometric matrix `S` and the
concentration trajectory obeys `c' = S * v(c)`, then the `l`-weighted
total at time `t` equals the `l`-weighted total at time `0`.

## i. Overview

This is constancy of the weighted total, not just that its derivative
vanishes: the derivative-zero fact (proved as in
`PhyslibExt.EarthScience.Stoichiometry`) is combined with the
mean-value constancy lemma `is_const_of_deriv_eq_zero`.

## ii. Key results

- `EarthScience.reaction_evolution_preserves_elemental_total`: the
  `l`-weighted total at time `t` equals that at time `0`.

## iii. References

- `HasDerivAt.fun_sum`, `HasDerivAt.const_mul`, `Finset.sum_comm` in
  Mathlib; `is_const_of_deriv_eq_zero` in
  `Mathlib/Analysis/Calculus/MeanValue.lean`.
-/

@[expose] public section

namespace EarthScience

/-- Reaction evolution preserves each conserved elemental total: if `l` is a
left-null vector of the stoichiometric matrix `S` and the concentration
trajectory obeys `c' = S * v(c)`, then the `l`-weighted total at time `t`
equals the `l`-weighted total at time `0`. -/
theorem reaction_evolution_preserves_elemental_total {n m : ℕ}
    (S : Fin n → Fin m → ℝ) (l : Fin n → ℝ)
    (c : ℝ → Fin n → ℝ) (rate : (Fin n → ℝ) → Fin m → ℝ) (t : ℝ)
    (hnull : ∀ j, ∑ i, l i * S i j = 0)
    (hode : ∀ i, ∀ s : ℝ, HasDerivAt (fun t => c t i) (∑ j, S i j * rate (c s) j) s) :
    ∑ i, l i * c t i = ∑ i, l i * c 0 i := by
  have hderiv0 : ∀ s : ℝ, HasDerivAt (fun t => ∑ i, l i * c t i) 0 s := by
    intro s
    have hval : (∑ i, l i * (∑ j, S i j * rate (c s) j)) = 0 := by
      calc ∑ i, l i * (∑ j, S i j * rate (c s) j)
          = ∑ i, ∑ j, l i * (S i j * rate (c s) j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
        _ = ∑ j, ∑ i, l i * (S i j * rate (c s) j) := Finset.sum_comm
        _ = ∑ j, (∑ i, l i * S i j) * rate (c s) j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring
        _ = 0 := by simp [hnull]
    have hsum : HasDerivAt (fun t => ∑ i, l i * c t i)
        (∑ i, l i * (∑ j, S i j * rate (c s) j)) s := by
      apply HasDerivAt.fun_sum
      intro i _
      exact (hode i s).const_mul (l i)
    rwa [hval] at hsum
  have hdiff : Differentiable ℝ (fun t => ∑ i, l i * c t i) :=
    fun s => (hderiv0 s).differentiableAt
  have hzero : ∀ s, deriv (fun t => ∑ i, l i * c t i) s = 0 :=
    fun s => (hderiv0 s).deriv
  exact is_const_of_deriv_eq_zero hdiff hzero t 0

end EarthScience
