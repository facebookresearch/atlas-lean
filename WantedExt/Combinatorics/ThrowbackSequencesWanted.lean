/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Instances.Real.Lemmas
public import MathlibExt.Combinatorics.Sequences.ThrowbackFrequency
public import MathlibExt.Combinatorics.Sequences.ThrowbackPerfectMixing
public import MathlibExt.Combinatorics.Sequences.ThrowbackRecurrence
public import MathlibExt.Combinatorics.Sequences.ThrowbackUniformRecurrence

/-!
# Throwback sequences of positive integers (Darnell, Dribus)

Statements from J. Darnell and B. F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1.

The throwback operation moves the leader `x₀` of a sequence `X = (x₀, x₁, …)` to index `x₀`:
`τ(X) = (x₁, …, x_{x₀}, x₀, x_{x₀+1}, …)`; the throwback sequence `T(X)` lists the leaders of
`τⁿ(X)`. The special case `X = (3, 4, 5, …)` (Kozar's conjecture for OEIS A357081) is proved as
`MetaMathlibExt.kozar_throwback_recurrence`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Recursive bound on the time to become leader.** Let $X = (x_0, x_1, \dots)$ be a sequence
of pairwise distinct positive integers, with positions numbered from $0$, the leader being at
position $0$. Let $\tau$ be the throwback and $T(X) = (t_0, t_1, \dots)$ the throwback
sequence, so $t_k$ is the leader of $\tau^k(X)$. Let $n \ge 1$, and let $N$ be the number of
indices $i$ with $x_i < n$. Suppose $a$ and $b$ are natural numbers such that for every
$m \ge 0$, the term at position $n - 1$ of $\tau^m(X)$ equals $t_{m+k}$ for some $k \le a$, and
the term at position $N$ of $\tau^m(X)$ equals $t_{m+k}$ for some $k \le b$. Then for every
$m \ge 0$, the term at position $n$ of $\tau^m(X)$ equals $t_{m+k}$ for some $k \le a + b + 1$.

This is the bound $M(n) \le M(n - 1) + M(N) + 1$ of the source, stated for upper bounds, where
$M(n)$ is the largest number of throwbacks the term at position $n$ of any $\tau^m(X)$ needs to
become leader.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Lemma 3 (`jis-2025-25.5.1-lem-3`). -/
public theorem_wanted throwback_leader_time_le (X : ℕ → ℕ) (hX : ∀ n, 0 < X n)
    (hinj : Function.Injective X) (n : ℕ) (hn : 0 < n) (a b : ℕ)
    (ha : ∀ m, ∃ k ≤ a, throwbackSequence X (m + k) = ((throwback id)^[m] X) (n - 1))
    (hb : ∀ m, ∃ k ≤ b,
      throwbackSequence X (m + k) = ((throwback id)^[m] X) (Set.ncard {i | X i < n})) :
    ∀ m, ∃ k ≤ a + b + 1, throwbackSequence X (m + k) = ((throwback id)^[m] X) n

open Classical in
/-- **Limiting frequencies in throwback sequences.** Let $X = (x_0, x_1, \dots)$ be a sequence of
pairwise distinct positive integers with throwback sequence $T(X) = (t_0, t_1, \dots)$, and for a
natural number $w$ let $\sigma(w)$ be the number of indices $i$ with $x_i < w$. Then for every
index $j$, writing $x = x_j$, the number of $k < N$ with $t_k = x$, divided by $N$, converges as
$N \to \infty$ to
$$f(x) = \frac{1}{x - \sigma(x) + 1} \prod_{w} \frac{w - \sigma(w)}{w - \sigma(w) + 1},$$
where the product runs over the values $w < x$ taken by $X$.

For a term $w$ of $X$, $\sigma(w)$ is the index of $w$ in the increasing rearrangement of $X$.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Theorem 4 (`jis-2025-25.5.1-thm-4`). -/
public theorem_wanted throwbackSequence_limiting_frequency (X : ℕ → ℕ) (hX : ∀ n, 0 < X n)
    (hinj : Function.Injective X) (j : ℕ) :
    Filter.Tendsto
      (fun N : ℕ =>
        ((((Finset.range N).filter fun k => throwbackSequence X k = X j).card : ℕ) : ℝ) / N)
      Filter.atTop
      (nhds (1 / ((X j : ℝ) - Set.ncard {i | X i < X j} + 1) *
        ∏ w ∈ Finset.range (X j),
          if w ∈ Set.range X then
            ((w : ℝ) - Set.ncard {i | X i < w}) / ((w : ℝ) - Set.ncard {i | X i < w} + 1)
          else 1))

/-- **Partial placement sequences are periodic.** Let $X = (x_0, x_1, \dots)$ be a strictly
increasing sequence of positive integers and let $n \ge 0$. Then the partial placement sequence
$P_n(X)$ is periodic: there is an integer $p > 0$ such that for every position
$z \in \mathbb{Z}$, the positions $z + p$ and $z$ of $P_n(X)$ are either both empty or hold the
same term.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Lemma 6 (`jis-2025-25.5.1-lem-6`). -/
public theorem_wanted partialPlacement_periodic (X : ℕ → ℕ) (hX : StrictMono X)
    (hX0 : 0 < X 0) (n : ℕ) :
    ∃ p : ℤ, 0 < p ∧ ∀ z, partialPlacement X n (z + p) = partialPlacement X n z

/-- **Minimal complete blocks of partial placements match configurations.** Let
$X = (x_0, x_1, \dots)$ be a strictly increasing sequence of positive integers, let $\tau$ be
the throwback, let $n \ge 0$, and write $P_n(X)_z$ for the entry, possibly empty, of the
partial placement sequence $P_n(X)$ at position $z \in \mathbb{Z}$. The minimal complete block
at $z$ is the word $P_n(X)_z, P_n(X)_{z+1}, \dots, P_n(X)_{z+L-1}$, empty positions included,
where $L$ is the least length for which these positions contain every $x_i$ with $i \le n$
($L = 0$ if there is no such length). Then for all natural numbers $k$ and $l$, the minimal
complete blocks at $k$ and at $l$ are equal if and only if each of $x_0, \dots, x_n$ occupies
the same positions in $\tau^k(X)$ as in $\tau^l(X)$. Moreover, for every $z \in \mathbb{Z}$ the
minimal complete block at $z$ equals the minimal complete block at some natural number $k$.
So minimal complete blocks of $P_n(X)$ correspond bijectively to the configurations of
$x_0, \dots, x_n$ in the sequences $\tau^k(X)$ with $k \ge 0$.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Lemma 8 (`jis-2025-25.5.1-lem-8`). -/
public theorem_wanted partialPlacement_minimal_complete_blocks_iff_configurations
    (X : ℕ → ℕ) (hX : StrictMono X) (hX0 : 0 < X 0) (n : ℕ) :
    let len : ℤ → ℕ := fun z =>
      sInf {L | ∀ i ≤ n, ∃ t < L, partialPlacement X n (z + t) = some (X i)}
    let block : ℤ → List (Option ℕ) := fun z =>
      (List.range (len z)).map fun t => partialPlacement X n (z + t)
    (∀ k l : ℕ, block k = block l ↔
      ∀ i ≤ n, ∀ p, (((throwback id)^[k] X) p = X i ↔ ((throwback id)^[l] X) p = X i)) ∧
      ∀ z : ℤ, ∃ k : ℕ, block z = block k

end

end MetaMathlibExt
