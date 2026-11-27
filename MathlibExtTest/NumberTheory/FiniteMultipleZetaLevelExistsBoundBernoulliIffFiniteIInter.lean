/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FiniteMultipleZetaLevelExistsBoundBernoulliIffFiniteIInter
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Rat.Lemmas

/-! # Tests for `FiniteMultipleZetaLevelExistsBoundBernoulliIffFiniteIInter` -/

namespace MathlibExtTest.NumberTheory.FiniteMultipleZetaLevelExistsBoundBernoulliIffFiniteIInter

-- Forward direction on `M = 7`: three odd indices `3, 5, 7` lie in `Icc 3 7`.
example (h : ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∃ k, Odd k ∧ 3 ≤ k ∧ k ≤ 7 ∧ k < p ∧ ¬ (p : ℤ) ∣ (bernoulli' (p - k)).num) :
    ∃ M : ℕ, 5 ≤ M ∧
      {p : ℕ | p.Prime ∧ ∀ k ∈ Finset.Icc 3 M, Odd k →
        k < p ∧ (p : ℤ) ∣ (bernoulli' (p - k)).num}.Finite :=
  MetaMathlibExt.exists_bound_bernoulli_iff_finite_iInter.mp ⟨7, h⟩

-- Backward direction on `M = 9`: four odd indices `3, 5, 7, 9` lie in `Icc 3 9`.
example (hfin : {p : ℕ | p.Prime ∧ ∀ k ∈ Finset.Icc 3 9, Odd k →
    k < p ∧ (p : ℤ) ∣ (bernoulli' (p - k)).num}.Finite) :
    ∃ M : ℕ, ∀ p : ℕ, p.Prime → 5 ≤ p →
      ∃ k, Odd k ∧ 3 ≤ k ∧ k ≤ M ∧ k < p ∧ ¬ (p : ℤ) ∣ (bernoulli' (p - k)).num :=
  MetaMathlibExt.exists_bound_bernoulli_iff_finite_iInter.mpr ⟨9, by decide, hfin⟩

-- Condition (a) at `p = 5`: the witness `k = 3` works, since `num(B_2) = 1`.
example : ¬ ((5 : ℕ) : ℤ) ∣ (bernoulli' (5 - 3)).num := by
  rw [show 5 - 3 = 2 from rfl, bernoulli'_two, one_div, Rat.inv_ofNat_num]; decide

-- Condition (a) at `p = 7`: the witness `k = 3` works, since `num(B_4) = -1`.
example : ¬ ((7 : ℕ) : ℤ) ∣ (bernoulli' (7 - 3)).num := by
  rw [show 7 - 3 = 4 from rfl, bernoulli'_four, neg_div, Rat.num_neg_eq_neg_num, one_div,
    Rat.inv_ofNat_num]; decide

-- Edge case of condition (b): a prime `p ≤ M` with `M` odd is never in the set,
-- because the index `k = M` violates `k < p`.
example : 7 ∉ {p : ℕ | p.Prime ∧ ∀ k ∈ Finset.Icc 3 7, Odd k →
    k < p ∧ (p : ℤ) ∣ (bernoulli' (p - k)).num} := by
  rintro ⟨-, h⟩
  exact lt_irrefl 7 (h 7 (by decide) (by decide)).1

end MathlibExtTest.NumberTheory.FiniteMultipleZetaLevelExistsBoundBernoulliIffFiniteIInter
