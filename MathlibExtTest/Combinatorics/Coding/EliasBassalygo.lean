/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Coding.EliasBassalygo

open MathlibExt.Combinatorics.Coding.EliasBassalygo

-- Binary, `n = 4`, `d = 2`, `e = 0`: `4 · 2 < 16`; every code of distance 2 has
-- `|C| · 1 ≤ 4 · 2 · 2^4`.
example (C : Finset (Fin 4 → Bool))
    (h : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → 2 ≤ hammingDist c₁ c₂) :
    C.card * ∑ i ∈ Finset.range (0 + 1), Nat.choose 4 i * (2 - 1) ^ i ≤ 4 * 2 * 2 ^ 4 := by
  simpa using card_mul_sum_le C (d := 2) (e := 0) (by norm_num) (by norm_num) h (by norm_num)

-- Binary, `n = d = 3`, `e = 1`: `(3 - 1)² = 4 > 0`; codes of distance 3 have `|C| · 4 ≤ 9 · 8`.
example (C : Finset (Fin 3 → Bool))
    (h : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → 3 ≤ hammingDist c₁ c₂) :
    C.card * ∑ i ∈ Finset.range (1 + 1), Nat.choose 3 i * (2 - 1) ^ i ≤ 3 * 3 * 2 ^ 3 := by
  simpa using card_mul_sum_le C (d := 3) (e := 1) (by norm_num) le_rfl h (by norm_num)
