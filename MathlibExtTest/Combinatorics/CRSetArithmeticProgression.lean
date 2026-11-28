/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.PNat.Basic
import MathlibExt.Combinatorics.CRSetArithmeticProgression

open MetaMathlibExt

-- At index zero only the first coordinate is constrained.
example {S : Type*} [AddCommSemigroup S] {A : Set S} (hA : IsCRSet A) :
    IsCRSet (Prod.fst ⁻¹' A : Set (S × S)) := by
  simpa [Nat.le_zero, Set.preimage] using hA.arithmeticProgressions 0

-- Positive naturals have no additive identity; all three terms are covered.
example {A : Set ℕ+} (hA : IsCRSet A) :
    IsCRSet {p : ℕ+ × ℕ+ | p.1 ∈ A ∧ p.1 + p.2 ∈ A ∧ p.1 + p.2 + p.2 ∈ A} := by
  have h : {p : ℕ+ × ℕ+ | ∀ i ≤ 2, (· + p.2)^[i] p.1 ∈ A} =
      {p : ℕ+ × ℕ+ | p.1 ∈ A ∧ p.1 + p.2 ∈ A ∧ p.1 + p.2 + p.2 ∈ A} := by
    ext p
    change (∀ i ≤ 2, (· + p.2)^[i] p.1 ∈ A) ↔
      p.1 ∈ A ∧ p.1 + p.2 ∈ A ∧ p.1 + p.2 + p.2 ∈ A
    constructor
    · intro hp
      exact ⟨hp 0 (by decide), hp 1 (by decide), hp 2 (by decide)⟩
    · rintro ⟨h₀, h₁, h₂⟩ i hi
      rcases i with _ | _ | _ | i
      · exact h₀
      · exact h₁
      · exact h₂
      · omega
  exact h ▸ hA.arithmeticProgressions 2
