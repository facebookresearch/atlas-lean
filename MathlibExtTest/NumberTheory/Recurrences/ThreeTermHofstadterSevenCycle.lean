/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.ThreeTermHofstadterSevenCycle

open MetaMathlibExt

-- The smallest parameters give an empty arbitrary block and just one new term.
-- The next term is 13, whereas extending the residue-1 formula would give 14.
example :
    let init : List ℤ := [1, 2, 3, 4, 5, 6, 7, 6, 12, 12, 5]
    threeTermHofstadterTerm true init 9 = some 12 ∧
      threeTermHofstadterTerm true init 12 = some 7 ∧
      threeTermHofstadterTerm true init 13 = some 13 := by
  decide

-- At the inclusive endpoint of the second full cycle, the middle seed is still arbitrary.
example (x : ℤ) :
    threeTermHofstadterTerm true
      ((List.range 17).map (fun i : ℕ => (i : ℤ) + 1) ++ [6] ++ [x] ++ [32, 34, 15]) 36 =
      some 15 := by
  exact threeTermHofstadter_sevenCycle (K := 17) (c := 2) (γ := 2) (lam := 0) (mu := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    [x] rfl 1 6 (by decide) (by decide) (by decide)
