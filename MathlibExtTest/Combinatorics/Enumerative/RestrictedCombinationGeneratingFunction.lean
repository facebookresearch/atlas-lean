/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RestrictedCombinationGeneratingFunction

open MetaMathlibExt

-- Forbidding zero has no effect. Adding one to each start gives the corresponding combination.
example : restrictedOverlapTilings {0, 2} 5 2 = {{0, 1}, {1, 2}} := by decide

example : restrictedCombinations {0, 2} 3 2 = {{1, 2}, {2, 3}} := by decide

-- Below the shift, the all-square tiling contributes exactly the constant polynomial one.
example : restrictedOverlapTilingCount {3} 2 0 = 1 ∧
    restrictedOverlapTilingCount {3} 2 1 = 0 ∧ restrictedOverlapTilingCount {3} 2 2 = 0 := by
  decide

-- With no forbidden differences, the two series agree without a correction term.
example :
    PowerSeries.mk (fun n => ∑ k ∈ Finset.range (n + 1),
        (restrictedCombinationCount ∅ n k : Polynomial ℤ) * Polynomial.X ^ k) =
      PowerSeries.mk (fun n => ∑ k ∈ Finset.range (n + 1),
        (restrictedOverlapTilingCount ∅ n k : Polynomial ℤ) * Polynomial.X ^ k) := by
  simpa using restrictedCombination_genFun_eq_tiling_genFun ∅
