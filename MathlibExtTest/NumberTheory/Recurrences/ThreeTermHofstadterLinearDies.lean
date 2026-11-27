/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.ThreeTermHofstadterLinearDies

open MetaMathlibExt

-- The theorem applies to the small starts and to both sides of the length-formula cutoff.
example : ∃ T, ThreeTermHofstadterEndsAfter false [1, 2, 3] T :=
  threeTermHofstadter_linear_dies (N := 3) (Or.inl rfl)

example : ∃ T, ThreeTermHofstadterEndsAfter false [1, 2, 3, 4] T :=
  threeTermHofstadter_linear_dies (N := 4) (Or.inr (Or.inl rfl))

example :
    ∃ T, ThreeTermHofstadterEndsAfter false ((List.range 10).map fun i : ℕ => (i : ℤ) + 1) T :=
  threeTermHofstadter_linear_dies (N := 10) (Or.inr (Or.inr le_rfl))

example :
    ∃ T, ThreeTermHofstadterEndsAfter false ((List.range 14).map fun i : ℕ => (i : ℤ) + 1) T :=
  threeTermHofstadter_linear_dies (N := 14) (Or.inr (Or.inr (by decide)))

-- For N = 13, the last computed term is 82; at index 74 it forces a negative lookup.
example :
    let init := (List.range 13).map fun i : ℕ => (i : ℤ) + 1
    threeTermHofstadterTerm false init 73 = some 82 ∧
      threeTermHofstadterTerm false init 74 = none := by
  decide +kernel
