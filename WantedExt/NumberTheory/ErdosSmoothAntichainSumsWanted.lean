/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 123
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosSmoothAntichainSumsWanted

/-! Source record `EP-123`. -/

/-- `IsSmoothForm a b c s` holds when `s = a ^ k * b ^ l * c ^ m` for some
`k l m : ℕ`. Zero exponents are allowed, so `1` is always a smooth form. -/
def IsSmoothForm (a b c s : ℕ) : Prop :=
  ∃ k l m : ℕ, s = a ^ k * b ^ l * c ^ m

/-- A finite set of naturals is a divisibility antichain when `s ∣ t` with
`s t ∈ S` forces `s = t`. -/
def Antichain (S : Finset ℕ) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, s ∣ t → s = t

/-- Erdős Problem 123: for pairwise coprime bases `a b c > 1`, every
sufficiently large integer is the sum of distinct smooth forms, no one of
which divides another. -/
def conjecture : Prop :=
  ∀ a b c : ℕ, 2 ≤ a → 2 ≤ b → 2 ≤ c →
    Nat.Coprime a b → Nat.Coprime b c → Nat.Coprime a c →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ S : Finset ℕ, (∀ s ∈ S, IsSmoothForm a b c s) ∧
        Antichain S ∧ S.sum id = n

/--
Resolved true: Resolved true: erdosproblems.com/123 records an affirmative resolution by GPT 5.6
(prompted by C. Snyder), accepted by the site and proved in Lean 4 (Erdos123.erdos_123, standard
axioms): for pairwise coprime a, b, c > 1 every large integer is a sum of distinct a^k b^l c^m,
none dividing another. Source: T. F. Bloom, Erdős Problem #123, erdosproblems.com (live page,
LaTeX source and forum threads read 2026-10-22), https://www.erdosproblems.com/123; T. F. Bloom,
summary of the proof of Erdős Problem #123, https://www.thomasbloom.org/erdos123.pdf. Moved from
`OpenConjectures/NumberTheory/ErdosSmoothAntichainSums`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosSmoothAntichainSumsWanted
