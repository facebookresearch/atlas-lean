/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Order.IncidenceAlgebra.PhilipHall

@[expose] public section

open Finset IncidenceAlgebra MathlibExt.Order.IncidenceAlgebra.PhilipHall

namespace MathlibExtTest.Order.IncidenceAlgebra.PhilipHall

/-- One chain of length `0` from an element to itself. -/
example : chainCount (2 : ℕ) 2 0 = 1 := by simp [chainCount_zero]

/-- No chain of length `0` between distinct elements. -/
example : chainCount (2 : ℕ) 5 0 = 0 := by simp [chainCount_zero]

/-- Chains between `0` and `2` in `ℕ` are too short to have length `3`. -/
example : chainCount (0 : ℕ) 2 3 = 0 :=
  chainCount_eq_zero_of_card_le (by simp)

/-- One chain of length `1` from `0` to `1` in `ℕ`: the recurrence for removing the last step. -/
example : chainCount (0 : ℕ) 1 1 = 1 := by
  rw [chainCount_succ]
  simp [chainCount_zero]

/-- Philip Hall's theorem on `ℕ`, the interval `[0, 1]`: `μ(0, 1) = c₀ - c₁ = -1`. -/
example : mu ℤ (0 : ℕ) 1 = -1 := by
  rw [mu_eq_sum_chainCount]
  simp [Finset.sum_range_succ, chainCount_zero, chainCount_succ]

/-- The bounded form applies to a finite chain. -/
example : eulerChar ℤ (Fin 3) =
    ∑ i ∈ range (Icc (⊥ : Fin 3) ⊤).card, (-1) ^ i * (chainCount (⊥ : Fin 3) ⊤ i : ℤ) :=
  eulerChar_eq_sum_chainCount ℤ

end MathlibExtTest.Order.IncidenceAlgebra.PhilipHall
