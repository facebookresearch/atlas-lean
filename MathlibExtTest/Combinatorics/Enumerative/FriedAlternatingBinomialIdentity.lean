/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FriedAlternatingBinomialIdentity

/-! # Tests for `MathlibExt.Combinatorics.Enumerative.FriedAlternatingBinomialIdentity` -/

namespace MathlibExtTest.FriedAlternatingBinomialIdentity

open MetaMathlibExt

/-- The binomial coefficient of the statement, extended by `0` to negative arguments. -/
private def C (a b : ℤ) : ℤ := if 0 ≤ a ∧ 0 ≤ b then (a.toNat.choose b.toNat : ℤ) else 0

/-- The left side of the identity. -/
private def lhs (n r s : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1) ^ k * C n k * C (2 * n - 2 * r) (n - k) * C (n - k) (n - 2 * r + s) *
      C (2 * r - k - s) (n - s)

/-- The right side of the identity. -/
private def rhs (n r s : ℕ) : ℤ := (-1) ^ n * C n (2 * r - n) * C (2 * n - 2 * r) (n - s)

-- The theorem's statement, with its local `C` unfolded, is `lhs n r s = rhs n r s`.
private theorem lhs_eq_rhs (n r s : ℕ) (hr : r ≤ n) (hs : s ≤ 2 * r) : lhs n r s = rhs n r s :=
  fried_alternating_binomial_identity n r s hr hs

-- The convention: `C` vanishes on negative arguments (also `C (-1) 0`) and above the diagonal.
example : C (-1) 0 = 0 ∧ C 2 (-1) = 0 ∧ C 2 3 = 0 ∧ C 5 2 = 10 := by decide

-- The hypotheses allow a nonzero value: at `n = 5`, `r = 3`, `s = 2` both sides evaluate to
-- `-20`; only the term `k = 2r - n = 1` of the sum is nonzero.
example : lhs 5 3 2 = -20 ∧ rhs 5 3 2 = -20 := by decide

-- The theorem replaces the seven-term sum at `n = 6`, `r = 4`, `s = 3` by `C 6 2 * C 4 3 = 60`.
example : lhs 6 4 3 = 60 := by
  rw [lhs_eq_rhs 6 4 3 (by decide) (by decide)]
  decide

-- An independent check by evaluation of every case with `n ≤ 5`.
example : ∀ n ≤ 5, ∀ r ≤ n, ∀ s ≤ 2 * r, lhs n r s = rhs n r s := by decide

-- With `r = s = n` the sum is `(-1) ^ n`.
example (n : ℕ) : lhs n n n = (-1) ^ n := by
  rw [lhs_eq_rhs n n n le_rfl (by omega), rhs, show (2 : ℤ) * n - n = n by omega,
    show (2 : ℤ) * n - 2 * n = 0 by omega, show (n : ℤ) - n = 0 by omega]
  simp [C]

-- Edge case: when `2r < n` the sum vanishes, because `C n (2r - n) = 0`.
example (n r s : ℕ) (h : 2 * r < n) (hs : s ≤ 2 * r) : lhs n r s = 0 := by
  have hC : C n (2 * r - n) = 0 := by
    simp only [C, show ¬((0 : ℤ) ≤ n ∧ (0 : ℤ) ≤ 2 * r - n) by omega, ↓reduceIte]
  rw [lhs_eq_rhs n r s (by omega) hs, rhs, hC]
  simp

-- Edge case: when `s > n` (possible with `s ≤ 2r`, e.g. `n = r = 2`, `s = 3`) the sum vanishes,
-- because `C (2n - 2r) (n - s) = 0`.
example (n r s : ℕ) (hr : r ≤ n) (hs : s ≤ 2 * r) (h : n < s) : lhs n r s = 0 := by
  have hC : C (2 * n - 2 * r) (n - s) = 0 := by
    simp only [C, show ¬((0 : ℤ) ≤ 2 * n - 2 * r ∧ (0 : ℤ) ≤ n - s) by omega, ↓reduceIte]
  rw [lhs_eq_rhs n r s hr hs, rhs, hC]
  simp

end MathlibExtTest.FriedAlternatingBinomialIdentity
