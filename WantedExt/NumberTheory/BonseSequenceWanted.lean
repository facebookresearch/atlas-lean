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
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import MathlibExt.NumberTheory.BonseSequence

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.BonseWanted

open Filter Topology

/-- **A sufficient condition for a Bonse sequence.** Let $a_0 < a_1 < a_2 < \cdots$ be a strictly
increasing sequence of positive integers and write $A_n = a_0 a_1 \cdots a_{n-1}$ for the product
of its first $n$ terms. If there is a real number $c > 2$ such that $\log A_n / \log a_n > c$ for
all sufficiently large $n$, then $a$ is a Bonse sequence.

The hypothesis is equivalent to $\liminf_n \log A_n / \log a_n > 2$, an infinite limit inferior
included. In the paper's 1-based indexing it reads $\liminf \log A_n / \log a_{n+1} > 2$ with
$A_n = a_1 \cdots a_n$.

Source: Diego Marques, "Bonse's Inequality along
Subsequences of Primes", Theorem 1. -/
theorem_wanted isBonseSeq_of_liminf_gt (a : ℕ → ℕ)
    (hmono : StrictMono a) (hpos : ∀ n, 1 ≤ a n)
    (hlim : ∃ c : ℝ, 2 < c ∧ ∀ᶠ n in atTop,
      c < Real.log (∏ k ∈ Finset.range n, (a k : ℝ)) /
        Real.log (a n)) :
    IsBonseSeq a

end MathlibExt.NumberTheory.BonseWanted
