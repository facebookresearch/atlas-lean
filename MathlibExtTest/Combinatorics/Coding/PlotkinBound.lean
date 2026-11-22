/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Coding.PlotkinBound

open MathlibExt.Combinatorics.Coding.PlotkinBound

/-- The binary repetition code of length 3. -/
def rep3 : Finset (Fin 3 → Bool) := {fun _ => false, fun _ => true}

theorem rep3_dist : ∀ c₁ ∈ rep3, ∀ c₂ ∈ rep3, c₁ ≠ c₂ → 3 ≤ hammingDist c₁ c₂ := by
  decide

-- Binary, `n = d = 3`: `q d = 6 > (q - 1) n = 3`, so `|C| · 3 ≤ 6`, i.e. at most two codewords.
example : rep3.card * (2 * 3 - (2 - 1) * 3) ≤ 2 * 3 :=
  card_mul_le (α := Bool) rep3 rep3_dist (by decide)

-- Ternary, `n = 2`, `d = 2`: `q d = 6 > 4`, so a code of distance 2 has at most `6 / 2 = 3`
-- words, attained by `{00, 11, 22}`.
example (C : Finset (Fin 2 → Fin 3))
    (h : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → 2 ≤ hammingDist c₁ c₂) :
    C.card * (3 * 2 - (3 - 1) * 2) ≤ 3 * 2 :=
  card_mul_le C h (by decide)

-- In one coordinate, at most half of the ordered pairs of binary words disagree.
example (C : Finset (Fin 3 → Bool)) (j : Fin 3) :
    2 * ∑ c ∈ C, ∑ c' ∈ C, (if c j ≠ c' j then (1 : ℕ) else 0) ≤ (2 - 1) * C.card ^ 2 :=
  card_mul_sum_ne_le C j
