/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.ThreeTermHofstadter

/-! # Tests for the length of the unpadded three-term Hofstadter sequence -/

open MetaMathlibExt

-- At the threshold, the last term is 39. The next step tries to read index zero.
example :
    let init := (List.range 14).map fun i : ℕ => (i : ℤ) + 1
    threeTermHofstadterTerm false init 38 = some 39 ∧
      threeTermHofstadterTerm false init 39 = none ∧
      threeTermHofstadterTerm true init 39 = some 33 := by
  decide

-- Just below the threshold, the term at N + 25 still exists.
example :
    threeTermHofstadterTerm false ((List.range 13).map fun i : ℕ => (i : ℤ) + 1) 38 = some 32 := by
  decide
