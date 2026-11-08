/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bonse's inequality along subsequences of primes

Statements from Diego Marques, "Bonse's Inequality along
Subsequences of Primes", *INTEGERS* 26 (2026), Article A99
(<https://math.colgate.edu/~integers/vol26.html>).

For a strictly increasing sequence `a` of positive
integers, write `Aₙ = a₁ ⋯ aₙ` and let `pₘ` be the `m`-th
prime (`p₁ = 2`); the sequence is a *Bonse sequence* if
`∏_{k ≤ n} p_{a_k} > p_{a_{n+1}}²` for all sufficiently
large `n` (this eventual form is the one the paper's proof
of Theorem 1 establishes: "it suffices to prove
`∑_{k=1}^n log p_{a_k} > 2 log p_{a_{n+1}}` for all
sufficiently large `n`"). Sequences here are indexed from
`0`, so the paper's `aₙ` is `a (n - 1)` below in
1-based terms: concretely `Aₙ` is `∏ k ∈ Finset.range n, a k`
and the paper's `a_{n+1}` is `a n`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.BonseWanted

open Filter Topology

/-- The `m`-th prime, 1-based (`primeNth 1 = 2`); junk
value `Nat.nth Nat.Prime 0 = 2` at `m = 0` is unused. -/
noncomputable def primeNth (m : ℕ) : ℕ := Nat.nth Nat.Prime (m - 1)

/-- Bonse sequence in the paper's sense: eventually
`∏_{k < n} p_{a_k} > p_{a_n}²` (0-based indexing, see the
module docstring). -/
def IsBonseSeq (a : ℕ → ℕ) : Prop :=
  ∀ᶠ n in atTop, (primeNth (a n) : ℝ) ^ 2 <
    ∏ k ∈ Finset.range n, (primeNth (a k) : ℝ)

/-- **Theorem 1**: if
`liminf (log Aₙ / log a_{n+1}) > 2` (stated with a finite
margin, which also covers the paper's `+∞` case: some
`c > 2` is eventually below the quotient), then `a` is
a Bonse sequence.

Source: Diego Marques, "Bonse's Inequality along
Subsequences of Primes", Theorem 1. -/
theorem_wanted isBonseSeq_of_liminf_gt (a : ℕ → ℕ)
    (hmono : StrictMono a) (hpos : ∀ n, 1 ≤ a n)
    (hlim : ∃ c : ℝ, 2 < c ∧ ∀ᶠ n in atTop,
      c < Real.log (∏ k ∈ Finset.range n, (a k : ℝ)) /
        Real.log (a n)) :
    IsBonseSeq a

/-- **Theorem 2**: if
`(n log log aₙ) / log a_{n+1} → 0` and
`liminf (log Aₙ / log a_{n+1}) < 2` (stated as: the
quotient is frequently below some `c < 2`), then `a` is
not a Bonse sequence.

Source: Diego Marques, "Bonse's Inequality along
Subsequences of Primes", Theorem 2. -/
theorem_wanted not_isBonseSeq_of_liminf_lt (a : ℕ → ℕ)
    (hmono : StrictMono a) (hpos : ∀ n, 1 ≤ a n)
    (hreg : Tendsto (fun n : ℕ =>
      ((n : ℝ) + 1) * Real.log (Real.log (a n)) /
        Real.log (a (n + 1))) atTop (𝓝 0))
    (hlim : ∃ c : ℝ, c < 2 ∧ ∃ᶠ n in atTop,
      Real.log (∏ k ∈ Finset.range n, (a k : ℝ)) /
        Real.log (a n) < c) :
    ¬ IsBonseSeq a

end MathlibExt.NumberTheory.BonseWanted
