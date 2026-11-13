/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Interval.Finset.Nat
public import Batteries.Util.ProofWanted

@[expose] public section

/-!
# Erdős Problem #883 (2)

For every `ℓ ≥ 1`, for all sufficiently large `n`, every threshold-sized
`A ⊆ {1, …, n}` has `G(A)` containing a complete tripartite graph with
part sizes `(1, ℓ, ℓ)`.
-/

namespace MathlibExt.NumberTheory.ErdosProblem883Question2Wanted

/-- Erdős threshold from EP-883: `⌊n/2⌋ + ⌊n/3⌋ - ⌊n/6⌋` via `ℕ` division (the same definition
as `ErdosProblem883.erdosThreshold` of the first question). -/
def erdosThreshold (n : ℕ) : ℕ :=
  n / 2 + n / 3 - n / 6

/-- Complete tripartite containment with part sizes `(1, ℓ, ℓ)` for the coprimality graph `G(A)`
of EP-883: a center `v₀` and disjoint `ℓ`-sets `L₁, L₂`, all in `A` and distinct, with every
cross-part pair coprime (the first question's `ContainsCompleteTripartite_1_ll`). -/
def ContainsCompleteTripartite1LL (A : Finset ℕ) (ell : ℕ) : Prop :=
  ∃ v₀ : ℕ, ∃ L₁ L₂ : Finset ℕ,
    v₀ ∈ A ∧ L₁ ⊆ A ∧ L₂ ⊆ A ∧
    L₁.card = ell ∧ L₂.card = ell ∧
    v₀ ∉ L₁ ∧ v₀ ∉ L₂ ∧ Disjoint L₁ L₂ ∧
    (∀ a ∈ L₁, Nat.Coprime v₀ a) ∧
    (∀ b ∈ L₂, Nat.Coprime v₀ b) ∧
    (∀ a ∈ L₁, ∀ b ∈ L₂, Nat.Coprime a b)

/-- Second question of EP-883: for every `ℓ ≥ 1`, for all sufficiently large
`n`, every `A ⊆ {1, …, n}` above the threshold has `G(A)` containing a
complete tripartite graph with part sizes `(1, ℓ, ℓ)`. -/
def Statement : Prop :=
  ∀ (ell : ℕ), 1 ≤ ell →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n → erdosThreshold n < A.card →
      ContainsCompleteTripartite1LL A ell

/--
Resolved true: Sárközy proved the complete-tripartite conclusion, in fact with part size growing
on the order of log n / log log n. Source: Gábor N. Sárközy, Complete tripartite subgraphs in
the coprime graph of integers, Discrete Mathematics 202 (1999), 227–238,
https://doi.org/10.1016/S0012-365X(98)00359-8; T. F. Bloom, Erdős Problem #883,
erdosproblems.com, https://www.erdosproblems.com/883. Moved from
`OpenConjectures/NumberTheory/ErdosProblem883Question2`.
-/
public theorem_wanted Statement_holds : Statement

end MathlibExt.NumberTheory.ErdosProblem883Question2Wanted
