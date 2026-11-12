/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
/-!
# Elemental conservation vectors annihilate the stoichiometric matrix

A vector `l` is a conservation vector for a stoichiometric matrix `S`
when `∑ i, l i * S i j = 0` for every reaction `j`. Such a vector
annihilates every stoichiometric change: for every reaction-extent
vector `ξ`, the weighted change `∑ i, l i * (∑ j, S i j * ξ j)` is `0`.

## i. Overview

This is the algebraic, extent form of stoichiometric conservation.
The ODE form (the weighted total of a concentration trajectory obeying
`c' = S * v(c)` has derivative `0`) is proved separately in
`PhyslibExt.EarthScience.Stoichiometry`.

## ii. Key results

- `EarthScience.elemental_conservation_vector_annihilates`: a conservation
  vector annihilates `S * ξ` for every extent vector `ξ`.

## iii. References

- `Finset.sum_comm`, `Finset.mul_sum`, `Finset.sum_mul` in Mathlib
  (`Mathlib/Algebra/BigOperators/`).
-/

@[expose] public section

namespace EarthScience

/-- An elemental conservation vector annihilates the stoichiometric matrix:
if `l` satisfies `∑ i, l i * S i j = 0` for every reaction `j`, then for every
reaction-extent vector `ξ`, the weighted stoichiometric change `∑ i, l i * (∑ j, S i j * ξ j)`
is zero. -/
theorem elemental_conservation_vector_annihilates {n m : ℕ}
    (S : Fin n → Fin m → ℝ) (l : Fin n → ℝ)
    (hnull : ∀ j, ∑ i, l i * S i j = 0)
    (ξ : Fin m → ℝ) :
    ∑ i, l i * (∑ j, S i j * ξ j) = 0 := by
  calc ∑ i, l i * (∑ j, S i j * ξ j)
      = ∑ i, ∑ j, l i * (S i j * ξ j) := by simp only [Finset.mul_sum]
    _ = ∑ i, ∑ j, (l i * S i j) * ξ j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact (mul_assoc _ _ _).symm
    _ = ∑ j, ∑ i, (l i * S i j) * ξ j := Finset.sum_comm
    _ = ∑ j, (∑ i, l i * S i j) * ξ j := by simp only [← Finset.sum_mul]
    _ = 0 := by simp only [hnull, zero_mul, Finset.sum_const_zero]

end EarthScience
