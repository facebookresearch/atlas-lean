/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquaresMultiplicativeAdditivePairedSquaresDichotomy
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace MathlibExtTest.NumberTheory.MultiplicativeAdditivePairedSquaresMultiplicativeAdditivePairedSquaresDichotomy

open MetaMathlibExt ArithmeticFunction

-- The identity arithmetic function realizes the left disjunct at `k = 5`.
example (n : ℕ) (hn : 0 < n) :
    (ArithmeticFunction.id : ArithmeticFunction ℂ) n = n := by
  obtain h | h := multiplicative_additive_paired_squares_dichotomy 5 (by decide) _
    isMultiplicative_id.natCast (fun x y _ _ ↦ by simp)
  · exact h n hn
  · have h2 := h 2 (Or.inl ⟨1, 1, by decide, by decide, rfl⟩)
    norm_num at h2

end MathlibExtTest.NumberTheory.MultiplicativeAdditivePairedSquaresMultiplicativeAdditivePairedSquaresDichotomy
