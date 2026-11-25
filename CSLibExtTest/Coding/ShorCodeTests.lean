/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.ShorCode

@[expose] public section

/-!
# Tests for Shor's nine-qubit code

* `|0̄⟩` and `|1̄⟩` have amplitude `1` on `|000000000⟩`, and amplitudes `1` and `-1` on
  `|111111111⟩` (three blocks `111`, so the sign `(-1)^3`): the codewords are nonzero and
  distinct.
* A basis state with a block other than `000`, `111` has amplitude `0`.
-/

namespace Cslib.CodingTheory.Shor.Tests

open Cslib.CodingTheory.CSS

example : shorCodeword 0 0 = 1 ∧ shorCodeword 1 0 = 1 := by
  simp [shorCodeword, sign_zero]

example : shorCodeword 0 1 = 1 ∧ shorCodeword 1 1 = -1 := by
  refine ⟨?_, ?_⟩
  · simp [shorCodeword, sign_zero]
  · simp only [shorCodeword, Pi.one_apply, and_self, ite_true]
    rw [show ((1 : ZMod 2) * (1 + 1 + 1)) = 1 by decide, sign_one]

example : shorCodeword 1 (Pi.single 0 1) = 0 := by
  simp [shorCodeword]

end Cslib.CodingTheory.Shor.Tests
