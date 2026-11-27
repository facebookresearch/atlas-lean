/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TribDigitMultiples

open MetaMathlibExt

-- The theorem applies at the smallest positive modulus, with both conclusions available.
example :
    (∃ m, 0 < m ∧ 1 ∣ m ∧ ¬ [1, 1, 1] <:+: Nat.digits 2 m) ∧
      ∃ m, 0 < m ∧ 1 ∣ m ∧ (∀ e ∈ Nat.digits 3 m, e ≤ 1) ∧ ¬ [1, 1, 1] <:+: Nat.digits 3 m :=
  exists_tribbinary_and_tribternary_multiple 1 (by decide)

-- Both bases share a factor with 6, and the two digit lists start with least significant zeros.
example : 0 < 84 ∧ 6 ∣ 84 ∧ ¬ [1, 1, 1] <:+: Nat.digits 2 84 := by
  have hdigits : Nat.digits 2 84 = [0, 0, 1, 0, 1, 0, 1] := by decide
  rw [hdigits]
  decide

example :
    0 < 30 ∧ 6 ∣ 30 ∧ (∀ e ∈ Nat.digits 3 30, e ≤ 1) ∧ ¬ [1, 1, 1] <:+: Nat.digits 3 30 := by
  have hdigits : Nat.digits 3 30 = [0, 1, 0, 1] := by decide
  rw [hdigits]
  exact ⟨by decide, by decide, by simp, by decide⟩
