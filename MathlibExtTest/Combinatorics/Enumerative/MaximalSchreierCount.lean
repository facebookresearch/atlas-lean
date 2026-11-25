/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.MaximalSchreierCount

/-!
# Tests for counts of maximal Schreier sets
-/

open MetaMathlibExt

-- Reducing 2/2 to 1/1 leaves just the singleton at n = 1.
example : maximalSchreierCount 2 2 1 = 1 :=
  ((maximalSchreierCount_formula_and_recurrence (p := 2) (q := 2)
    (by decide) (by decide)).1 1).trans (by decide)

-- The last admissible index contributes one set with no room between its interior elements.
example : maximalSchreierCount 2 4 8 = 12 :=
  ((maximalSchreierCount_formula_and_recurrence (p := 2) (q := 4)
    (by decide) (by decide)).1 8).trans (by decide)

-- At its first index the unreduced recurrence has two signed terms and the singleton delay.
example : (maximalSchreierCount 2 2 5 : ℤ) =
    2 * maximalSchreierCount 2 2 4 - maximalSchreierCount 2 2 3 + maximalSchreierCount 2 2 1 := by
  apply ((maximalSchreierCount_formula_and_recurrence (p := 2) (q := 2)
    (by decide) (by decide)).2 5 (by decide)).trans
  decide
