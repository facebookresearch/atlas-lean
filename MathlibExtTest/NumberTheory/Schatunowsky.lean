/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Schatunowsky

/-! # Tests for Schatunowsky's theorem -/

open MetaMathlibExt

-- The largest listed value satisfies the coprimality criterion.
example {b : ℕ} (hb : 1 < b) (hlt : b < 30) (hcop : Nat.Coprime 30 b) : b.Prime := by
  have h : 30 ∈ {a : ℕ | 2 ≤ a ∧ ∀ k : ℕ, 1 < k → k < a → a.Coprime k → k.Prime} := by
    rw [nat_schatunowsky]
    simp
  exact h.2 b hb hlt hcop

-- Beyond the last listed value there is always a smaller composite coprime to the input.
example {a : ℕ} (ha : 30 < a) : ∃ b : ℕ, 1 < b ∧ b < a ∧ a.Coprime b ∧ ¬ b.Prime := by
  by_contra! h
  have hmem : a ∈ {n : ℕ | 2 ≤ n ∧ ∀ b : ℕ, 1 < b → b < n → n.Coprime b → b.Prime} :=
    ⟨by omega, h⟩
  rw [nat_schatunowsky] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  omega
