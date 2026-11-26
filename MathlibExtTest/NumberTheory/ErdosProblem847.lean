/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.ErdosProblem847

/-! The public statements retain their previous names and remain definitionally unchanged. -/

open MathlibExt.NumberTheory.ErdosProblem847Wanted

example (A : Set ℕ) : HasFew3APs A ↔
    ∃ ε : ℝ, 0 < ε ∧ ∀ B : Set ℕ, B ⊆ A → Finite B →
      ∃ C : Set ℕ, C ⊆ B ∧ ε * B.ncard ≤ C.ncard ∧ ThreeAPFree C := Iff.rfl

example : conjecture ↔
    ∀ A : Set ℕ, Infinite A → HasFew3APs A →
      ∃ n, ∃ S : Fin n → Set ℕ, (∀ i, ThreeAPFree (S i)) ∧ A = ⋃ i : Fin n, S i := Iff.rfl

example : ¬ conjecture := conjecture_refuted

example : ∃ A : Set ℕ, Infinite A ∧ HasFew3APs A ∧
    ¬ (∃ n, ∃ S : Fin n → Set ℕ, (∀ i, ThreeAPFree (S i)) ∧ A = ⋃ i : Fin n, S i) := by
  classical
  by_contra h
  apply conjecture_refuted
  intro A hA hFew
  by_contra hCover
  exact h ⟨A, hA, hFew, hCover⟩
