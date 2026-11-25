/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RemainderSet
import Mathlib.Order.Filter.Cofinite

/-!
# Tests for sets of remainders and unbounded drops in their size
-/

namespace MetaMathlibExt

-- The remainder sets of `11` and `12` (Table 1 of the paper): the count drops from `4` to `2`.
example : remainderSet 11 = {0, 1, 2, 3} ∧ remainderSet 12 = {0, 2} := by
  decide

-- Edge cases: there are no moduli for `n ≤ 1`, and `S(2) = {0}`.
example : remainderSet 0 = ∅ ∧ remainderSet 1 = ∅ ∧ remainderSet 2 = {0} := by
  decide

-- A drop of `3` from `n = 131`: `132 = 3 · 44 = 4 · 33 = 12 · 11 = 132 · 1` uses the primes
-- `2, 3, 11, 131`, so four remainders of `131` are not shifted into `S(132)`.
example : remainderCount 131 = 33 ∧ remainderCount 132 = 30 := by
  decide +kernel

-- The main theorem gives drops of any size beyond any bound.
example : ∃ n ≥ 10 ^ 6, remainderCount (n + 1) + 100 ≤ remainderCount n :=
  Filter.frequently_atTop.1 (remainderCount_drops_unbounded 100) (10 ^ 6)

-- Equivalently, for every `M` the set of `n` with a drop of at least `M` is infinite.
example (M : ℕ) : {n | remainderCount (n + 1) + M ≤ remainderCount n}.Infinite :=
  Nat.frequently_atTop_iff_infinite.1 (remainderCount_drops_unbounded M)

-- So `s(n + 1) - s(n)` has no lower bound, as `liminf (s(n + 1) - s(n)) = -∞` says.
example : ¬ ∃ C : ℤ, ∀ n : ℕ, C ≤ (remainderCount (n + 1) : ℤ) - remainderCount n := by
  rintro ⟨C, hC⟩
  obtain ⟨n, -, hn⟩ :=
    Filter.frequently_atTop.1 (remainderCount_drops_unbounded ((-C).toNat + 1)) 0
  have := hC n
  omega

end MetaMathlibExt
