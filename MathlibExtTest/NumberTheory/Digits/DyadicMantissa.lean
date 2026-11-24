/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.DyadicMantissa
import Mathlib.Tactic.NormNum

/-! # Tests for Girgensohn's lemma on dyadic mantissas -/

namespace MetaMathlibExt.dyadicMantissa_wellDefined_iff_doubling_invariant

-- A doubling-invariant function agrees at `3` and `12`, whose mantissas are both `1 / 2`.
example (G : ℕ → ℝ) (hG : ∀ n : ℕ, 0 < n → G (2 * n) = G n) : G 3 = G 12 := by
  refine (dyadicMantissa_wellDefined_iff_doubling_invariant G).2 hG 3 12 (by norm_num)
    (by norm_num) ?_
  rw [show Nat.log 2 3 = 1 by decide, show Nat.log 2 12 = 3 by decide]
  norm_num

-- The mantissa itself is a function of the mantissa, so it is invariant under doubling.
example (n : ℕ) (hn : 0 < n) :
    (((2 * n : ℕ) : ℚ) - 2 ^ Nat.log 2 (2 * n)) / 2 ^ Nat.log 2 (2 * n) =
      ((n : ℚ) - 2 ^ Nat.log 2 n) / 2 ^ Nat.log 2 n := by
  have h := (dyadicMantissa_wellDefined_iff_doubling_invariant
    fun k => ((((k : ℚ) - 2 ^ Nat.log 2 k) / 2 ^ Nat.log 2 k : ℚ) : ℝ)).1
    (fun _ _ _ _ hmn => by rw [hmn]) n hn
  exact_mod_cast h

-- The identity is not invariant under doubling, so it does not factor through the mantissa:
-- `1` and `2` have the same mantissa `0`.
example : ¬ ∀ m n : ℕ, 0 < m → 0 < n →
    ((m : ℚ) - 2 ^ Nat.log 2 m) / 2 ^ Nat.log 2 m =
      ((n : ℚ) - 2 ^ Nat.log 2 n) / 2 ^ Nat.log 2 n → (m : ℝ) = n := by
  rw [dyadicMantissa_wellDefined_iff_doubling_invariant fun n => (n : ℝ)]
  intro h
  have h1 := h 1 one_pos
  norm_num at h1

end MetaMathlibExt.dyadicMantissa_wellDefined_iff_doubling_invariant
