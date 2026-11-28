/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EvenPseudoprimeReciprocalWindow
import Mathlib.Tactic.NormNum.Prime

namespace MetaMathlibExt.EvenPseudoprimeReciprocalWindowTest

-- The order of `2` modulo `7` is `3`, so the modulus is `21`.
example : orderOf (2 : ZMod 7) = 3 :=
  orderOf_eq_prime (by decide) (by decide)

-- For `p = 7`, the reciprocal sum over the window `e ^ k < N ≤ e ^ (k + 1)` of the residue
-- class `N ≡ 7 [MOD 21]` with `N > 7` is at most `2 / 21`, for every `k`.
open scoped Classical in
example (k : ℕ) :
    ∑ N ∈ (Finset.Icc 1 ⌊Real.exp (k + 1)⌋₊).filter (fun N : ℕ =>
        Real.exp k < N ∧ N ≡ 7 [MOD 21] ∧ 7 < N), (1 : ℝ) / N ≤ 2 / 21 := by
  have h3 : orderOf (2 : ZMod 7) = 3 := orderOf_eq_prime (by decide) (by decide)
  have := sum_inv_modEq_orderOf_le (p := 7) (by norm_num) (by norm_num) k
  rw [h3] at this
  norm_num at this ⊢
  exact this

end MetaMathlibExt.EvenPseudoprimeReciprocalWindowTest
