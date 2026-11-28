/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FiniteMultipleZetaLevelExistsBoundFermatQuotientIffFiniteIInter

/-! # Tests for the uniform bound criterion for non-Wieferich bases -/

-- For a prime at the cutoff `M = 3`, the fallback base `p + 1` works even beyond `M`.
example : Nat.Prime 3 ∧ ∃ N : ℕ, 3 < N ∧ N ≤ 4 ∧ ¬ 3 ∣ N ∧ ¬ 3 ^ 2 ∣ N ^ (3 - 1) - 1 :=
  ⟨by decide, 4, by decide, by decide, by decide, by decide⟩

-- The exceptional prime `2` already fails the condition for membership at base `2`.
example : 2 ∉ {p : ℕ | p.Prime ∧ ∀ N ∈ Finset.Icc 2 3, p ^ 2 ∣ N ^ (p - 1) - 1} := by
  rintro ⟨-, h⟩
  exact (by decide : ¬ (2 : ℕ) ^ 2 ∣ 2 ^ (2 - 1) - 1) (h 2 (by decide))

-- For `11`, base `3` satisfies the divisibility test but base `2` does not.
example : (11 : ℕ) ^ 2 ∣ 3 ^ (11 - 1) - 1 := by decide

example : 11 ∉ {p : ℕ | p.Prime ∧ ∀ N ∈ Finset.Icc 2 3, p ^ 2 ∣ N ^ (p - 1) - 1} := by
  rintro ⟨-, h⟩
  exact (by decide : ¬ (11 : ℕ) ^ 2 ∣ 2 ^ (11 - 1) - 1) (h 2 (by decide))

-- For `1093 > 3`, base `2` satisfies the test, and base `3` is a coprime witness that fails it.
set_option exponentiation.threshold 2048 in
set_option maxRecDepth 100000 in
example : Nat.Prime 1093 ∧ (1093 : ℕ) ^ 2 ∣ 2 ^ (1093 - 1) - 1 ∧
    ∃ N : ℕ, N ∈ Finset.Icc 2 3 ∧ ¬ 1093 ∣ N ∧ ¬ 1093 ^ 2 ∣ N ^ (1093 - 1) - 1 :=
  ⟨by decide, by decide, 3, by decide, by decide, by decide⟩

-- A client can convert finiteness at bases `2, 3` into the existence of a uniform bound.
example (hfin : {p : ℕ | p.Prime ∧ ∀ N ∈ Finset.Icc 2 3, p ^ 2 ∣ N ^ (p - 1) - 1}.Finite) :
    ∃ M : ℕ, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∃ N, 1 ≤ N ∧ N ≤ M ∧ ¬ p ∣ N ∧ ¬ p ^ 2 ∣ N ^ (p - 1) - 1 :=
  MetaMathlibExt.exists_bound_fermatQuotient_iff_finite_iInter.mpr ⟨3, le_rfl, hfin⟩
