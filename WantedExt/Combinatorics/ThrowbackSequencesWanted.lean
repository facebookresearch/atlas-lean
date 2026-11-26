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
public import MathlibExt.Combinatorics.Sequences.ThrowbackLeaderTime
public import MathlibExt.Combinatorics.Sequences.ThrowbackPeriodicity
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
