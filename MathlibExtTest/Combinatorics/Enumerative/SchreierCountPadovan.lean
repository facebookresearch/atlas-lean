/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SchreierCountPadovan

/-!
# Tests for Schreier counts as Padovan-like sequences
-/

open MetaMathlibExt

-- No set with maximum `1` is `(3, 2)`-Schreier, maximal or not.
example : schreierCount 3 2 1 = 0 ∧ maximalSchreierCount 3 2 1 = 0 := by
  decide +kernel

-- At `n = 1` both counts are the Padovan value at index `0`.
example : schreierCount 1 1 1 = 1 ∧ maximalSchreierCount 1 1 1 = 1 := by
  have h := schreierCount_eq_schreierPadovan (p := 1) (q := 1) (n := 1)
    (by decide) (by decide) (by decide)
  exact ⟨h.1.trans (by decide +kernel), h.2.trans (by decide +kernel)⟩

-- At `n = 5` the `(2, 3)` counts are the Padovan values at index `12`.
example : schreierCount 2 3 5 = 7 ∧ maximalSchreierCount 2 3 5 = 2 := by
  have h := schreierCount_eq_schreierPadovan (p := 2) (q := 3) (n := 5)
    (by decide) (by decide) (by decide)
  exact ⟨h.1.trans (by decide +kernel), h.2.trans (by decide +kernel)⟩
