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

/-- **The $m$-th prime, counted from one.** For $m \ge 1$, $p_m$ is the $m$-th prime, so that
$p_1 = 2$, $p_2 = 3$, $p_3 = 5$; at $m = 0$ the value is also $2$. -/
noncomputable def primeNth (m : ℕ) : ℕ := Nat.nth Nat.Prime (m - 1)

/-- **Bonse sequence of prime indices.** For $m \ge 1$ let $p_m$ be the $m$-th prime, so that
$p_1 = 2$, and set $p_0 = 2$. A sequence $a_0, a_1, a_2, \ldots$ of natural numbers is a Bonse
sequence if $p_{a_n}^2 < p_{a_0} p_{a_1} \cdots p_{a_{n-1}}$ for all sufficiently large $n$.

In the paper's 1-based indexing the condition reads $p_{a_1} \cdots p_{a_n} > p_{a_{n+1}}^2$ for
all sufficiently large $n$. -/
def IsBonseSeq (a : ℕ → ℕ) : Prop :=
  ∀ᶠ n in atTop, (primeNth (a n) : ℝ) ^ 2 <
    ∏ k ∈ Finset.range n, (primeNth (a k) : ℝ)

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

/-- **A sufficient condition for a non-Bonse sequence.** Let $a_0 < a_1 < a_2 < \cdots$ be a
strictly increasing sequence of positive integers and write $A_n = a_0 a_1 \cdots a_{n-1}$ for the
product of its first $n$ terms. Suppose that $(n + 1) \log \log a_n / \log a_{n+1} \to 0$ as
$n \to \infty$, and that there is a real number $c < 2$ such that $\log A_n / \log a_n < c$ for
infinitely many $n$. Then $a$ is not a Bonse sequence.

The second hypothesis is equivalent to $\liminf_n \log A_n / \log a_n < 2$. In the paper's
1-based indexing the hypotheses read $n \log \log a_n / \log a_{n+1} \to 0$ and
$\liminf \log A_n / \log a_{n+1} < 2$ with $A_n = a_1 \cdots a_n$.

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
