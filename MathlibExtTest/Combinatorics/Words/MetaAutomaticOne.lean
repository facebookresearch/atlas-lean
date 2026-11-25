/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.MetaAutomaticOne

open MetaMathlibExt

-- The initial pair and the first nested pair have opposite orientations.
example : [0, 1, 2, 3].map metaAutomaticOne = [false, true, true, false] := by
  decide +kernel

-- In these blocks the nested index selects the even and odd positions, respectively.
example : [26, 27, 30, 31].map metaAutomaticOne = [false, true, true, false] := by
  decide +kernel

-- Either value at an even index determines the following value.
example (n : ℕ) : metaAutomaticOne (2 * n + 1) = !metaAutomaticOne (2 * n) := by
  have h := metaAutomaticOne_balanced n
  cases he : metaAutomaticOne (2 * n) <;> cases ho : metaAutomaticOne (2 * n + 1) <;>
    simp_all
