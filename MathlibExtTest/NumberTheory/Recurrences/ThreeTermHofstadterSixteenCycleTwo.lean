/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.ThreeTermHofstadterSixteenCycleTwo

open MetaMathlibExt

-- Compute across the seed boundary, then check both sides of the cutoff.
example :
    let init : List ℤ := [-100, 16, 51, 7, 53, 49, 16, 49, 16, 50, 10, 54, 51, 7, 49, 16, 52]
    threeTermHofstadterTerm true init 17 = some 52 ∧
      threeTermHofstadterTerm true init 18 = some 16 ∧
      threeTermHofstadterTerm true init 19 = some 102 ∧
      threeTermHofstadterTerm true init 49 = some 352 ∧
      threeTermHofstadterTerm true init 50 = some (-84) := by
  decide

-- The residue-zero formula holds at the cutoff for every value of the arbitrary initial term.
example (x : ℤ) :
    threeTermHofstadterTerm true
      ([x] ++ [16, 51, 7, 53, 49, 16, 49, 16, 50, 10, 54, 51, 7, 49, 16, 52]) 49 =
      some 352 := by
  exact threeTermHofstadter_sixteenCycle_two (K := 1) (lam := 49) (mu₁ := 50) (mu₂ := 51)
    (ga₁ := 52) (ga₂ := 53) (ga₃ := 54) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) [x] rfl 3 0 (by decide) (by decide) (by decide)
