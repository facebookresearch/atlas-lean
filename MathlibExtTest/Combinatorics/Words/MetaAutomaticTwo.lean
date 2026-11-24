/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.MetaAutomaticTwo

open MetaMathlibExt

-- The two base values and the first pair defined by the recurrence.
example : [0, 1, 2, 3].map metaAutomaticTwo = [false, true, true, false] := by
  decide +kernel

-- At block indices 5 and 7 the nested selector takes both Boolean values.
example : [20, 21, 22, 23, 28, 29, 30, 31].map metaAutomaticTwo =
    [true, false, false, true, false, true, true, false] := by
  decide +kernel

example (n : ℕ) : metaAutomaticTwo (2 * n + 1) = !metaAutomaticTwo (2 * n) := by
  have h := metaAutomaticTwo_balanced n
  cases he : metaAutomaticTwo (2 * n) <;> cases ho : metaAutomaticTwo (2 * n + 1) <;>
    simp_all
