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

/-- **Parts of a partition in decreasing order.** For a partition $p$ of $n$ with $\ell$ parts,
this is the list $x_1 \ge x_2 \ge \cdots \ge x_\ell$ of the parts of $p$, each repeated according
to its multiplicity, sorted in weakly decreasing order.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 1 (weakly decreasing bargraphs). -/
public def decreasingParts {n : ℕ} (p : Nat.Partition n) : List ℕ :=
  p.parts.sort (· ≥ ·)

/-- **Lit cells of a weakly increasing bargraph.** For a partition $p$ of $n$, the number of lit
cells of $p$, drawn as a weakly increasing bargraph, is defined as the largest part of $p$ plus the
number of parts of $p$ minus the number of distinct parts of $p$ (the largest part of the empty
partition is $0$).

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 3, proof of Proposition 1. -/
public def litCellsIncreasing {n : ℕ} (p : Nat.Partition n) : ℕ :=
  p.parts.sup + p.parts.card - p.parts.dedup.card

/-- **Lit nodes of a partition.** The number of lit nodes of a partition $p$, drawn as a weakly
increasing Ferrers diagram of nodes, is defined as the largest part of $p$ plus the number of
parts of $p$ minus one; for the empty partition it is $0$.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 3, proof of Proposition 2. -/
public def litNodesIncreasing {n : ℕ} (p : Nat.Partition n) : ℕ :=
  p.parts.sup + p.parts.card - 1

/-- **Lit cells of a weakly decreasing bargraph.** Let $p$ be a partition of $n$ with $\ell$
parts $x_1 \ge x_2 \ge \cdots \ge x_\ell$. The number of lit cells of $p$, drawn as a weakly
decreasing bargraph, is defined as $\max_{1 \le i \le \ell} (x_i + i - 1)$, and as $0$ when $p$
has no parts. It is the largest part of the image of $p$ under Prodinger's bijection
$x_i \mapsto x_i + i - 1$.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 5. -/
public def litCellsDecreasing {n : ℕ} (p : Nat.Partition n) : ℕ :=
  ((decreasingParts p).mapIdx fun i x => x + i).foldr max 0

/-- **Triangular $q$-binomial coefficient.** For natural numbers $r$ and $s$, the triangular
$q$-binomial coefficient $t[r, s] \in \mathbb{Z}[[q]]$ is the power series whose coefficient of
$q^n$ is the number of partitions of $n$ with exactly $s$ parts $x_1 \ge \dots \ge x_s$ that fit
in the staircase with column heights $r, r - 1, \dots, r - s + 1$, that is, with
$x_i + (i - 1) \le r$ for $1 \le i \le s$.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 4. -/
public noncomputable def triangularQBinomial (r s : ℕ) : ℤ⟦X⟧ :=
  mk fun n => ((Finset.univ.filter fun p : Nat.Partition n =>
    p.parts.card = s ∧ ∀ i < s, (decreasingParts p).getD i 0 + i ≤ r).card : ℤ)

/-- **Triangle partition series.** For a natural number $r$, the triangle partition series is the
power series $T_q(r) = \sum_{s=0}^{r} t[r, s] \in \mathbb{Z}[[q]]$, where $t[r, s]$ is the
triangular $q$-binomial coefficient. It is the generating function of partitions contained in the
triangle with column heights $r, r - 1, \dots, 1$.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Definition 1. -/
public noncomputable def trianglePartitionSeries (r : ℕ) : ℤ⟦X⟧ :=
  ∑ s ∈ Finset.range (r + 1), triangularQBinomial r s

/-- **Lit cells of a one-part increasing bargraph.** For every natural number $n \ge 1$, the
partition $(n)$ of $n$ with a single part has $n$ lit cells as a weakly increasing bargraph.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 3 (definition of lit cells). -/
public theorem litCellsIncreasing_indiscrete {n : ℕ} (hn : n ≠ 0) :
    litCellsIncreasing (Nat.Partition.indiscrete n) = n := by
  simp [litCellsIncreasing, hn]

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

/-- **Triangular $q$-binomial coefficients with no parts.** For every natural number $r$, the
triangular $q$-binomial coefficient satisfies $t[r, 0] = 1$: only the empty partition has no
parts.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 4, initial conditions (10). -/
public theorem triangularQBinomial_zero_right (r : ℕ) : triangularQBinomial r 0 = 1 := by
  ext n
  rw [triangularQBinomial, coeff_mk, coeff_one]
  split_ifs with h
  · subst h
    rw [Nat.cast_eq_one, Finset.card_eq_one]
    refine ⟨default, ?_⟩
    ext p
    simp [Subsingleton.elim p default]
  · rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    have h0 : p.parts = 0 := Multiset.card_eq_zero.mp hp.1
    have := p.parts_sum
    rw [h0, Multiset.sum_zero] at this
    exact h this.symm

/-- **Triangle partition series at zero.** The triangle partition series $T_q(r)$ at $r = 0$
equals $1$, that is, $T_q(0) = 1$ in $\mathbb{Z}[[q]]$.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Definition 1. -/
public theorem trianglePartitionSeries_zero : trianglePartitionSeries 0 = 1 := by
  simp [trianglePartitionSeries, triangularQBinomial_zero_right]

/-- **Generating function for lit cells of weakly increasing bargraphs.** Let
$P(q) = \sum_{n \ge 0} p(n) q^n$ be the partition generating function, and let
$L(q) \in \mathbb{Z}[[q]]$ be the power series whose coefficient of $q^n$ is the total number of
lit cells over all partitions of $n$ drawn as weakly increasing bargraphs. Then
$$L(q) = 2P(q) \sum_{i \ge 1} \frac{q^i}{1 - q^i} - P(q) \frac{q}{1 - q}$$
and
$$L(q) = P(q) \sum_{i \ge 1} \frac{q^i (1 + q^i)}{1 - q^i},$$
where the sums converge coefficientwise.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Proposition 1, eq. (5)
(`integers-2024-A56-prop-1`). -/
public theorem_wanted litCellsIncreasing_generatingFunction :
    let P : ℤ⟦X⟧ := mk fun n => (Fintype.card (Nat.Partition n) : ℤ)
    mk (fun n => ∑ p : Nat.Partition n, (litCellsIncreasing p : ℤ)) =
        2 * P * ∑' i : ℕ, X ^ (i + 1) * invOfUnit (1 - X ^ (i + 1)) 1 -
          P * X * invOfUnit (1 - X) 1 ∧
      mk (fun n => ∑ p : Nat.Partition n, (litCellsIncreasing p : ℤ)) =
        P * ∑' i : ℕ, X ^ (i + 1) * (1 + X ^ (i + 1)) * invOfUnit (1 - X ^ (i + 1)) 1

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

/-- **Recursion for triangular $q$-binomial coefficients.** The triangular $q$-binomial
coefficients $t[r, s] \in \mathbb{Z}[[q]]$ satisfy the recursion
$t[r, s] = q^s \sum_{i=0}^{s} t[r - 1, i]$ for all natural numbers $r \ge 1$ and $s \le r$,
together with the initial conditions $t[1, 1] = q$, $t[2, 1] = q(1 + q)$, $t[r, 0] = 1$ for
every $r$, and $t[r, s] = 0$ whenever $r < s$.

The recursion is stated for $s \le r$ only: for $s > r$ the left side is $0$, while the right
side is $q^s \sum_{i=0}^{r-1} t[r - 1, i] \ne 0$; for example $t[1, 2] = 0$ but
$q^2 (t[0, 0] + t[0, 1] + t[0, 2]) = q^2$.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Proposition 3, eqs. (9), (10)
(`integers-2024-A56-prop-3`). -/
public theorem_wanted triangularQBinomial_recursion :
    (∀ r s : ℕ, s ≤ r + 1 →
      triangularQBinomial (r + 1) s = X ^ s * ∑ i ∈ Finset.range (s + 1), triangularQBinomial r i) ∧
    triangularQBinomial 1 1 = X ∧ triangularQBinomial 2 1 = X * (1 + X) ∧
    (∀ r, triangularQBinomial r 0 = 1) ∧ ∀ r s, r < s → triangularQBinomial r s = 0

/-- **Triangular $q$-binomial coefficients via Gaussian binomials.** For natural numbers $r$ and
$s$ with $1 \le r$ and $s \le r$, the triangular $q$-binomial coefficient $t[r, s]$ satisfies
$$
t[r, s] = q^s \binom{r + s - 1}{s}_q - q^{s+1} \sum_{i=2}^{s} t[i - 1, i - 1] \,
q^{i(r - i)} \binom{r + 1 + s - 2i}{s - i}_q
$$
in $\mathbb{Z}[[q]]$, where $\binom{M}{k}_q$ denotes the Gaussian binomial coefficient.

In the range $s \le r$ every exponent and binomial index above is a natural number; for $s > r$
one has $t[r, s] = 0$.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Proposition 4, eq. (12)
(`integers-2024-A56-prop-4`). -/
public theorem_wanted triangularQBinomial_eq_gaussBinom_sub {r s : ℕ} (hr : 1 ≤ r)
    (hs : s ≤ r) :
    triangularQBinomial r s =
      X ^ s * MathlibExt.gaussBinom X (r + s - 1) s -
        X ^ (s + 1) * ∑ i ∈ Finset.Icc 2 s, triangularQBinomial (i - 1) (i - 1) *
          X ^ (i * (r - i)) * MathlibExt.gaussBinom X (r + 1 + s - 2 * i) (s - i)

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

/-- **Lit cells when only the first column is lit.** For a partition $p$ of $n$ with $\ell \ge 1$
parts $x_1 \ge x_2 \ge \cdots \ge x_\ell$, say that only the first column of its weakly
decreasing bargraph is lit when the number of lit cells of $p$ equals its largest part $x_1$,
that is, when $x_i + i - 1 \le x_1$ for $1 \le i \le \ell$. Let $F(q) \in \mathbb{Z}[[q]]$ be
the power series whose coefficient of $q^n$ is the sum of $x_1$ over the partitions of $n$ in
which only the first column is lit and $x_1 \ge 2$. For $r \ge 0$ let $T_q(r)$ be the
generating function of partitions contained in the triangle with column heights
$r, r - 1, \ldots, 1$. Then
$$F(q) = \sum_{r \ge 1} (r + 1) q^{r+1} T_q(r),$$
where the sum converges coefficientwise.

The condition $x_1 \ge 2$ is the range $r \ge 1$ of the paper's
$T(u, q) = \sum_{r \ge 1} u^{r+1} q^{r+1} T_q(r)$; among the partitions in which only the first
column is lit it excludes only $(1)$.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Proposition 6 (`integers-2024-A56-prop-6`). -/
public theorem_wanted litCellsDecreasing_firstColumn_generatingFunction :
    (mk fun n => ∑ p ∈ Finset.univ.filter (fun p : Nat.Partition n =>
        litCellsDecreasing p = p.parts.sup ∧ 2 ≤ p.parts.sup), (p.parts.sup : ℤ)) =
      ∑' r : ℕ, ((r + 2 : ℕ) : ℤ⟦X⟧) * X ^ (r + 2) * trianglePartitionSeries (r + 1)

end

end MetaMathlibExt
