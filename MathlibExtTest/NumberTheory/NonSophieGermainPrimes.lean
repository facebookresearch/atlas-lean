/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NonSophieGermainPrimes

open MetaMathlibExt

-- The first term of the progression for 5 is 7.
example : 7 ∈ {q : ℕ | q.Prime ∧ ¬ q.IsSophieGermainPrime} := by
  rw [setOf_prime_not_isSophieGermainPrime_eq_inter]
  exact ⟨by decide, 5, 1, by decide, by decide, by decide, rfl⟩

-- Allowing index zero would put 2 in the progression for 5.
example : ¬ ∃ p r : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ r ∧ 2 = p * r + (p - 1) / 2 := by
  intro h
  have hmem : 2 ∈ {q : ℕ | q.Prime ∧ ¬ q.IsSophieGermainPrime} := by
    rw [setOf_prime_not_isSophieGermainPrime_eq_inter]
    exact ⟨by decide, h⟩
  exact hmem.2 ⟨by decide, by decide⟩
