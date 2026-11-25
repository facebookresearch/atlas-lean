/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Schatunowsky

/-! # Tests for Schatunowsky's theorem and Iwata's generalization -/

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

-- Finiteness supplies a uniform threshold, beyond which a coprime witness always exists.
example (ℓ : ℕ) : ∃ N : ℕ, ∀ a > N,
    ∃ b : ℕ, 1 < b ∧ b < a ∧ a.Coprime b ∧ ℓ < ArithmeticFunction.cardFactors b := by
  obtain ⟨N, hN⟩ := (nat_iwata_finite ℓ).bddAbove
  refine ⟨N, fun a ha => ?_⟩
  by_contra! h
  exact ha.not_ge (hN h)

-- At bound zero the exceptional set consists exactly of 0, 1 and 2.
example : {a : ℕ | ∀ b : ℕ, 1 < b → b < a → a.Coprime b →
    ArithmeticFunction.cardFactors b ≤ 0} = Set.Iic 2 := by
  ext a
  constructor
  · intro ha
    change a ≤ 2
    by_contra! h
    have hb : 1 < a - 1 := by omega
    have hcop : a.Coprime (a - 1) := (Nat.coprime_self_sub_right (by omega)).mpr (by simp)
    exact (ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hb).not_ge
      (ha (a - 1) hb (by omega) hcop)
  · intro ha b hb hlt
    have : a ≤ 2 := ha
    omega
