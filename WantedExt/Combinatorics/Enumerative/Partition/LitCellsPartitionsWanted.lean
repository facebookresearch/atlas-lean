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

/-- The parts of a partition listed in weakly decreasing order `x_1 ≥ x_2 ≥ ⋯`.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 1 (weakly decreasing bargraphs). -/
public def decreasingParts {n : ℕ} (p : Nat.Partition n) : List ℕ :=
  p.parts.sort (· ≥ ·)

/-- The number of lit cells of a partition drawn as a weakly increasing bargraph: the largest
part plus the number of parts minus the number of distinct parts.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 3, proof of Proposition 1. -/
public def litCellsIncreasing {n : ℕ} (p : Nat.Partition n) : ℕ :=
  p.parts.sup + p.parts.card - p.parts.dedup.card

/-- The number of lit nodes of a partition drawn as a weakly increasing Ferrers diagram of
nodes: the largest part plus the number of parts minus one (`0` for the empty partition).

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 3, proof of Proposition 2. -/
public def litNodesIncreasing {n : ℕ} (p : Nat.Partition n) : ℕ :=
  p.parts.sup + p.parts.card - 1

/-- The number of lit cells of a partition drawn as a weakly decreasing bargraph
`x_1 ≥ x_2 ≥ ⋯`: `max_i (x_i + i - 1)`, the largest part of its image under Prodinger's
bijection `x_i ↦ x_i + i - 1` (`0` for the empty partition).

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 5. -/
public def litCellsDecreasing {n : ℕ} (p : Nat.Partition n) : ℕ :=
  ((decreasingParts p).mapIdx fun i x => x + i).foldr max 0

/-- The triangular `q`-binomial coefficient `t[r, s]`: the generating function of partitions
with exactly `s` parts `x_1 ≥ ⋯ ≥ x_s` contained in the staircase with column heights
`r, r - 1, …, r - s + 1`, i.e. `x_i + (i - 1) ≤ r` for `1 ≤ i ≤ s`.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 4. -/
public noncomputable def triangularQBinomial (r s : ℕ) : ℤ⟦X⟧ :=
  mk fun n => ((Finset.univ.filter fun p : Nat.Partition n =>
    p.parts.card = s ∧ ∀ i < s, (decreasingParts p).getD i 0 + i ≤ r).card : ℤ)

/-- `T_q(r) = ∑_{s=0}^{r} t[r, s]`, the generating function of partitions contained in the
triangle `r, r - 1, …, 1`.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Definition 1. -/
public noncomputable def trianglePartitionSeries (r : ℕ) : ℤ⟦X⟧ :=
  ∑ s ∈ Finset.range (r + 1), triangularQBinomial r s

/-- The one-part partition `(n)`, `n ≥ 1`, has `n` lit cells as a weakly increasing bargraph.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 3 (definition of lit cells). -/
public theorem litCellsIncreasing_indiscrete {n : ℕ} (hn : n ≠ 0) :
    litCellsIncreasing (Nat.Partition.indiscrete n) = n := by
  simp [litCellsIncreasing, hn]

/-- The one-part partition `(n)`, `n ≥ 1`, has `n` lit nodes.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 3 (definition of lit nodes). -/
public theorem litNodesIncreasing_indiscrete {n : ℕ} (hn : n ≠ 0) :
    litNodesIncreasing (Nat.Partition.indiscrete n) = n := by
  simp [litNodesIncreasing, hn]

/-- The one-part partition `(n)`, `n ≥ 1`, has `n` lit cells as a weakly decreasing bargraph.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 5 (lit cells of decreasing partitions). -/
public theorem litCellsDecreasing_indiscrete {n : ℕ} (hn : n ≠ 0) :
    litCellsDecreasing (Nat.Partition.indiscrete n) = n := by
  simp [litCellsDecreasing, decreasingParts, hn]

/-- `t[r, 0] = 1`: only the empty partition has no parts.

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

/-- `T_q(0) = 1`.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Definition 1. -/
public theorem trianglePartitionSeries_zero : trianglePartitionSeries 0 = 1 := by
  simp [trianglePartitionSeries, triangularQBinomial_zero_right]

/-- The total number of lit cells over all weakly increasing partitions of `n` has generating
function `2P(q) ∑_{i ≥ 1} q^i/(1 - q^i) - P(q) q/(1 - q) = P(q) ∑_{i ≥ 1} q^i(1 + q^i)/(1 - q^i)`.

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

/-- The total number of lit nodes over all weakly increasing partitions of `n` has generating
function `1 + P(q) (∑_{i ≥ 1} 2q^i/(1 - q^i) - 1)`.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Proposition 2, eq. (7)
(`integers-2024-A56-prop-2`). -/
public theorem_wanted litNodesIncreasing_generatingFunction :
    mk (fun n => ∑ p : Nat.Partition n, (litNodesIncreasing p : ℤ)) =
      1 + (mk fun n => (Fintype.card (Nat.Partition n) : ℤ)) *
        (∑' i : ℕ, 2 * X ^ (i + 1) * invOfUnit (1 - X ^ (i + 1)) 1 - 1)

/-- The recursion `t[r, s] = q^s ∑_{i=0}^{s} t[r - 1, i]` for `1 ≤ r` and `s ≤ r`, with the
initial conditions `t[1, 1] = q`, `t[2, 1] = q(1 + q)`, `t[r, 0] = 1` and `t[r, s] = 0` for
`s > r`. The recursion is stated for `s ≤ r` only: for `s > r` the left side is `0` while the
right side is `q^s T_q(r - 1) ≠ 0` (e.g. `t[1, 2] = 0` but `q² (t[0, 0] + t[0, 1] + t[0, 2]) = q²`);
the initial conditions cover `s > r`.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Proposition 3, eqs. (9), (10)
(`integers-2024-A56-prop-3`). -/
public theorem_wanted triangularQBinomial_recursion :
    (∀ r s : ℕ, s ≤ r + 1 →
      triangularQBinomial (r + 1) s = X ^ s * ∑ i ∈ Finset.range (s + 1), triangularQBinomial r i) ∧
    triangularQBinomial 1 1 = X ∧ triangularQBinomial 2 1 = X * (1 + X) ∧
    (∀ r, triangularQBinomial r 0 = 1) ∧ ∀ r s, r < s → triangularQBinomial r s = 0

/-- For `1 ≤ r` and `s ≤ r`,
`t[r, s] = q^s [r + s - 1, s]_q - q^{s+1} ∑_{i=2}^{s} t[i - 1, i - 1] q^{i(r-i)} [r - 2i + 1 + s, s - i]_q`.
The range `s ≤ r` is where every exponent and binomial index is a natural number (for `s > r`,
`t[r, s] = 0` by the initial conditions (10)); `r ≥ 1` makes `r + s - 1` a natural number.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Proposition 4, eq. (12)
(`integers-2024-A56-prop-4`). -/
public theorem_wanted triangularQBinomial_eq_gaussBinom_sub {r s : ℕ} (hr : 1 ≤ r)
    (hs : s ≤ r) :
    triangularQBinomial r s =
      X ^ s * MathlibExt.gaussBinom X (r + s - 1) s -
        X ^ (s + 1) * ∑ i ∈ Finset.Icc 2 s, triangularQBinomial (i - 1) (i - 1) *
          X ^ (i * (r - i)) * MathlibExt.gaussBinom X (r + 1 + s - 2 * i) (s - i)

/-- For `s ≤ k`, the generating function `lit[k, s]` of weakly decreasing partitions with at
most `s + 1` parts and at most `k` lit cells is
`∑_{i=0}^{s} t[s, i] q^{i(k-s)} [k + 1 - i, k - s]_q`.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Proposition 5, eq. (13)
(`integers-2024-A56-prop-5`). -/
public theorem_wanted litCellsDecreasing_le_generatingFunction {k s : ℕ} (hsk : s ≤ k) :
    (mk fun n => ((Finset.univ.filter fun p : Nat.Partition n =>
        p.parts.card ≤ s + 1 ∧ litCellsDecreasing p ≤ k).card : ℤ)) =
      ∑ i ∈ Finset.range (s + 1), triangularQBinomial s i * X ^ (i * (k - s)) *
        MathlibExt.gaussBinom X (k + 1 - i) (k - s)

/-- The total number of lit cells over all weakly decreasing partitions of `n` has generating
function `L(q) = ∑_{k ≥ 0} (P(q) - T_q(k))` (a sum in the coefficientwise topology).

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Theorem 1, eq. (16)
(`integers-2024-A56-thm-1`). -/
public theorem_wanted litCellsDecreasing_generatingFunction :
    mk (fun n => ∑ p : Nat.Partition n, (litCellsDecreasing p : ℤ)) =
      ∑' k : ℕ, ((mk fun n => (Fintype.card (Nat.Partition n) : ℤ)) - trianglePartitionSeries k)

/-- The total number of lit cells over the weakly decreasing partitions of `n` in which only
the first column is lit, i.e. `x_i + i - 1 ≤ x_1` for all `i` (so the lit cells are the `x_1`
cells of the first column), and whose first column has height `r + 1 ≥ 2`, has generating
function `∑_{r ≥ 1} (r + 1) q^{r+1} T_q(r)`. The height condition is the range `r ≥ 1` of the
paper's `T(u, q) = ∑_{r ≥ 1} u^{r+1} q^{r+1} T_q(r)`; it excludes only the partition `(1)`.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Proposition 6 (`integers-2024-A56-prop-6`). -/
public theorem_wanted litCellsDecreasing_firstColumn_generatingFunction :
    (mk fun n => ∑ p ∈ Finset.univ.filter (fun p : Nat.Partition n =>
        litCellsDecreasing p = p.parts.sup ∧ 2 ≤ p.parts.sup), (p.parts.sup : ℤ)) =
      ∑' r : ℕ, ((r + 2 : ℕ) : ℤ⟦X⟧) * X ^ (r + 2) * trianglePartitionSeries (r + 1)

end

end MetaMathlibExt
