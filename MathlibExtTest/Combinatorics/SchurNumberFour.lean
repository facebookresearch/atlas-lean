/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SchurNumberFour

/-! # Tests for `MathlibExt.Combinatorics.SchurNumberFour` -/

namespace MathlibExtTest.SchurNumberFour

open Finset MathlibExt.Combinatorics.SchurNumbersWanted

/-- For four colours, the least forcing endpoint is `45`, one past the Schur number. -/
private theorem isLeast_forces_four : IsLeast {N | schurForces 4 N} 45 := by
  have h := schurNumber_four
  rw [schurNumber, ite_eq_right (by decide)] at h
  have hinf : sInf {N | schurForces 4 N} = 44 + 1 := by omega
  simpa only [hinf] using isLeast_csInf (Nat.nonempty_of_sInf_eq_succ hinf)

-- Every colouring with four colours has a monochromatic solution in `[1, 45]`.
example : schurForces 4 45 := isLeast_forces_four.1

-- The value is not a junk value: no `N ≤ 44` forces a monochromatic solution, so some colouring
-- of `{1, …, 44}` with four colours has none.
example {N : ℕ} (hN : N ≤ 44) : ¬ schurForces 4 N := fun h => by
  have := isLeast_forces_four.2 h
  omega

-- The Schur numbers computed so far increase.
example : schurNumber 3 < schurNumber 4 := by
  rw [schurNumber_three, schurNumber_four]
  decide

/-- A colouring with four colours and no monochromatic solution in `[1, 44]`. -/
private def colouring (n : ℕ) : Fin 4 :=
  if n ∈ ({1, 3, 5, 15, 17, 19, 26, 28, 40, 42, 44} : Finset ℕ) then 0
  else if n ∈ ({2, 7, 8, 18, 21, 24, 27, 33, 37, 38, 43} : Finset ℕ) then 1
  else if n ∈ ({4, 6, 13, 20, 22, 23, 25, 30, 32, 39, 41} : Finset ℕ) then 2 else 3

private theorem colouring_sumFree : ∀ x ∈ Icc 1 44, ∀ y ∈ Icc 1 44, x + y ≤ 44 →
    colouring x = colouring y → colouring y ≠ colouring (x + y) := by
  decide +kernel

-- Extending this colouring to `45` necessarily creates a monochromatic solution `x + y = 45`.
example : ∃ x ∈ Icc 1 45, ∃ y ∈ Icc 1 45,
    x + y = 45 ∧ colouring x = colouring y ∧ colouring y = colouring 45 := by
  obtain ⟨x, hx, y, hy, z, hz, rfl, h1, h2⟩ := isLeast_forces_four.1 colouring
  have hz' := (mem_Icc.1 hz).2
  by_cases h45 : x + y = 45
  · exact ⟨x, hx, y, hy, h45, h1, h45 ▸ h2⟩
  · exact absurd h2 (colouring_sumFree x (mem_Icc.2 ⟨(mem_Icc.1 hx).1, by omega⟩) y
      (mem_Icc.2 ⟨(mem_Icc.1 hy).1, by omega⟩) (by omega) h1)

end MathlibExtTest.SchurNumberFour
