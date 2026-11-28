/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.ThreeTermHofstadterSixteenCycleOne

/-! # Tests for the first sixteen-cycle of the padded three-term Hofstadter-like recurrence -/

open MetaMathlibExt

private def init : List ℤ :=
  [-100, 58, 7, 61, 16, 61, 16, 59, 58, 7, 61, 16, 122, 16, 61, 25, 67, 58, 7]

-- Check the first seed, the corrected residue-12 seed, and the end of the initial block.
example : threeTermHofstadterTerm true init 2 = some 58 ∧
    threeTermHofstadterTerm true init 13 = some 122 ∧
    threeTermHofstadterTerm true init 17 = some 67 ∧
    threeTermHofstadterTerm true init 19 = some 7 := by
  decide

-- The first sixteen computed terms cover every residue, including all three shifts by 25.
example : (List.range' 20 16).map (threeTermHofstadterTerm true init) =
    ([122, 16, 122, 16, 118, 58, 7, 122, 16, 244, 16, 122, 25, 126, 58, 7] : List ℤ).map some := by
  decide

-- Residue 12 keeps doubling; the pattern reaches the cutoff but need not continue past it.
example : threeTermHofstadterTerm true init 45 = some 488 ∧
    threeTermHofstadterTerm true init 58 = some 7 ∧
    threeTermHofstadterTerm true init 59 = some 388 := by
  decide

-- Check padded lookups before and after a push, including old and out-of-range indices.
example : threeTermHofstadterLookup true (#[6].push 9) 0 = some 0 ∧
    threeTermHofstadterLookup true (#[6].push 9) 1 = some 6 ∧
    threeTermHofstadterLookup true (#[6].push 9) 2 = some 9 ∧
    threeTermHofstadterLookup true (#[6].push 9) 3 = none := by
  decide

-- The same known predecessors can produce a term or an undefined lookup, depending on padding.
example : threeTermHofstadterNext true #[1, 2, 7] = some 9 ∧
    threeTermHofstadterNext false #[1, 2, 7] = none := by
  decide

-- At residue 0 of cycle 2, the arbitrary prefix does not affect the first 25-step jump.
example (x : ℤ) :
    threeTermHofstadterTerm true
      ([x] ++ [58, 7, 61, 16, 61, 16, 59, 58, 7, 61, 16, 122, 16, 61, 25, 67, 58, 7]) 33 =
      some 126 := by
  exact threeTermHofstadter_sixteenCycle_one (K := 1) (lam := 58) (mu₁ := 59) (mu₂ := 61)
    (ga := 67) (by decide) (by decide) (by decide) (by decide) (by decide)
    [x] rfl 2 0 (by decide) (by decide) (by decide)
