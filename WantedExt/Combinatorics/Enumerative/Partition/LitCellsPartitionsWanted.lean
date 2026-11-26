/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Multiset.Sort
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import MathlibExt.Combinatorics.Enumerative.GaussianBinomial
public import MathlibExt.Combinatorics.Enumerative.Partition.LitCellsDecreasing
public import MathlibExt.Combinatorics.Enumerative.Partition.LitCellsIncreasing
public import MathlibExt.Combinatorics.Enumerative.Partition.TriangularQBinomial

/-!
# Lit cells in integer partitions — wishlist

Statements from Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on
Integer Partitions*, INTEGERS 24 (2024), Article A56.

A partition is drawn as a bargraph (column `i` has height `x_i`) lit by the sun at infinity in
the northwest. The paper reduces the number of lit cells to statistics of the parts, and we
take these reductions, stated in the paper's text, as the definitions:

* weakly increasing order (proof of Proposition 1): lit cells = largest part + number of
  parts − number of distinct parts (`litCellsIncreasing`);
* weakly increasing order, nodes (proof of Proposition 2): lit nodes = largest part + number
  of parts − 1 (`litNodesIncreasing`; `0` for the empty partition);
* weakly decreasing order `x_1 ≥ x_2 ≥ ⋯` (Section 5, via Prodinger's bijection
  `x_i ↦ x_i + i - 1`): lit cells = `max_i (x_i + i - 1)` (`litCellsDecreasing`).

`t[r, s]` (`triangularQBinomial r s`) is the generating function of partitions with exactly
`s` parts fitting under the staircase `r, r - 1, …, r - s + 1`, i.e. with `x_i ≤ r - i + 1`,
and `T_q(r) = ∑_{s=0}^{r} t[r, s]` (`trianglePartitionSeries r`, Definition 1). The Gaussian
binomial `[M, k]_q` is `MathlibExt.gaussBinom X M k`, and `P(q) = ∑ p(n) qⁿ`. Generating
functions are integer power series; the Lambert series `∑_{i ≥ 1} q^i / (1 - q^i)` are sums in
the coefficientwise topology.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- **Lit nodes of a partition.** The number of lit nodes of a partition $p$, drawn as a weakly
increasing Ferrers diagram of nodes, is defined as the largest part of $p$ plus the number of
parts of $p$ minus one; for the empty partition it is $0$.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 3, proof of Proposition 2. -/
public def litNodesIncreasing {n : ℕ} (p : Nat.Partition n) : ℕ :=
  p.parts.sup + p.parts.card - 1

/-- **Lit nodes of a one-part partition.** For every natural number $n \ge 1$, the one-part
partition $(n)$ of $n$ has exactly $n$ lit nodes.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 3 (definition of lit nodes). -/
public theorem litNodesIncreasing_indiscrete {n : ℕ} (hn : n ≠ 0) :
    litNodesIncreasing (Nat.Partition.indiscrete n) = n := by
  simp [litNodesIncreasing, hn]

/-- **Lit cells of a one-part decreasing bargraph.** For every natural number $n \ge 1$, the
partition $(n)$ of $n$ with a single part has $n$ lit cells as a weakly decreasing bargraph.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 5 (lit cells of decreasing partitions). -/
public theorem litCellsDecreasing_indiscrete {n : ℕ} (hn : n ≠ 0) :
    litCellsDecreasing (Nat.Partition.indiscrete n) = n := by
  simp [litCellsDecreasing, decreasingParts, hn]

/-- **Triangle partition series at zero.** The triangle partition series $T_q(r)$ at $r = 0$
equals $1$, that is, $T_q(0) = 1$ in $\mathbb{Z}[[q]]$.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Definition 1. -/
public theorem trianglePartitionSeries_zero : trianglePartitionSeries 0 = 1 := by
  simp [trianglePartitionSeries, triangularQBinomial_zero_right]

/-- **Generating function for lit nodes of weakly increasing diagrams.** Let
$P(q) = \sum_{n \ge 0} p(n) q^n$ be the partition generating function, and let
$N(q) \in \mathbb{Z}[[q]]$ be the power series whose coefficient of $q^n$ is the total number of
lit nodes over all partitions of $n$ drawn as weakly increasing Ferrers diagrams of nodes. Then
$$N(q) = 1 + P(q) \Bigl(\sum_{i \ge 1} \frac{2q^i}{1 - q^i} - 1\Bigr),$$
where the sum converges coefficientwise.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Proposition 2, eq. (7)
(`integers-2024-A56-prop-2`). -/
public theorem_wanted litNodesIncreasing_generatingFunction :
    mk (fun n => ∑ p : Nat.Partition n, (litNodesIncreasing p : ℤ)) =
      1 + (mk fun n => (Fintype.card (Nat.Partition n) : ℤ)) *
        (∑' i : ℕ, 2 * X ^ (i + 1) * invOfUnit (1 - X ^ (i + 1)) 1 - 1)

/-- **Lit cells of weakly decreasing partitions with few parts.** Let $k$ and $s$ be natural
numbers with $s \le k$. Write $\binom{M}{m}_q$ for the Gaussian binomial coefficient, and $t[s, i]$
for the triangular $q$-binomial coefficient: the generating function of partitions with exactly
$i$ parts $x_1 \ge \cdots \ge x_i$ such that $x_j + j - 1 \le s$ for $1 \le j \le i$. Let
$\mathrm{lit}[k, s] \in \mathbb{Z}[[q]]$ be the power series whose coefficient of $q^n$ is the
number of partitions of $n$ with at most $s + 1$ parts and at most $k$ lit cells as weakly
decreasing bargraphs. Then
$$\mathrm{lit}[k, s] = \sum_{i=0}^{s} t[s, i] \, q^{i(k-s)} \binom{k + 1 - i}{k - s}_q.$$

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Proposition 5, eq. (13)
(`integers-2024-A56-prop-5`). -/
public theorem_wanted litCellsDecreasing_le_generatingFunction {k s : ℕ} (hsk : s ≤ k) :
    (mk fun n => ((Finset.univ.filter fun p : Nat.Partition n =>
        p.parts.card ≤ s + 1 ∧ litCellsDecreasing p ≤ k).card : ℤ)) =
      ∑ i ∈ Finset.range (s + 1), triangularQBinomial s i * X ^ (i * (k - s)) *
        MathlibExt.gaussBinom X (k + 1 - i) (k - s)

/-- **Generating function for lit cells of weakly decreasing bargraphs.** Let
$P(q) = \sum_{n \ge 0} p(n) q^n$ be the partition generating function, for $k \ge 0$ let $T_q(k)$
be the generating function of partitions contained in the triangle with column heights
$k, k - 1, \ldots, 1$ (so $T_q(0) = 1$), and let $L(q) \in \mathbb{Z}[[q]]$ be the power series
whose coefficient of $q^n$ is the total number of lit cells over all partitions of $n$ drawn as
weakly decreasing bargraphs. Then
$$L(q) = \sum_{k \ge 0} \bigl(P(q) - T_q(k)\bigr),$$
where the sum converges coefficientwise.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Theorem 1, eq. (16)
(`integers-2024-A56-thm-1`). -/
public theorem_wanted litCellsDecreasing_generatingFunction :
    mk (fun n => ∑ p : Nat.Partition n, (litCellsDecreasing p : ℤ)) =
      ∑' k : ℕ, ((mk fun n => (Fintype.card (Nat.Partition n) : ℤ)) - trianglePartitionSeries k)

end

end MetaMathlibExt
