/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ArndtLastPart

open MetaMathlibExt

-- Only the empty composition has last part zero.
example : arndtLastPartCount 0 0 = 1 ∧ arndtLastPartCount 0 1 = 0 ∧
    arndtLastPartCount 3 0 = 0 := by decide

-- A singleton is admissible. The pair (2, 2) is excluded, and (3, 2) is admissible.
example : arndtLastPartCount 2 2 = 1 ∧ arndtLastPartCount 4 2 = 0 ∧
    arndtLastPartCount 5 2 = 2 := by decide

-- At m = 1 the odd- and even-length contributions have the same leading term.
example : Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (arndtLastPartCount n 1 : ℝ))
    (fun n : ℕ => Real.goldenRatio ^ ((n : ℤ) - 1 - 2) / Real.sqrt 5 * 2) := by
  simpa [one_add_one_eq_two] using arndtLastPartCount_isEquivalent 1 (by decide)
