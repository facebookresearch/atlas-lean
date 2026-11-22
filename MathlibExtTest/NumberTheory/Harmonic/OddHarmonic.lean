/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Harmonic.OddHarmonic
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MetaMathlibExt

example : oddHarmonic 0 = 0 := oddHarmonic_zero
example : oddHarmonic 3 = 23 / 15 := by
  simp [oddHarmonic, Finset.sum_range_succ]
  norm_num
example (n : ℕ) : oddHarmonic n = harmonic (2 * n) - harmonic n / 2 := oddHarmonic_eq_harmonic n

end MetaMathlibExt
