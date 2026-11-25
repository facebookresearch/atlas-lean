/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ColumnWeight

/-!
# Weights of even tables

This file defines even tables and their weights as used in the combinatorial expansion of random
determinant moments.

The source is Dominik Beck, Zelin Lv, and Aaron Potechin, *The Sixth Moment of Random
Determinants*, Journal of Integer Sequences 26 (2023), Article 23.6.3,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Lv/lv3.tex>, SHA-256
`b7561d53b71f40dc02aa6a65b56e1c93c202ea58e9067ccbe04a021a9dee97b0`.

Provenance: statement `jis_27d3ea8c4aa1d31860d82adf`, semantic concept
`jis_sem_fb63c6b5f1a68ced5b0d9660`.
-/

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-- **Even table.** For natural numbers $k$ and $n$, an even $k \times n$ table is a $k \times n$
array of entries from $\{0, 1, \dots, n-1\}$ such that $k$ is even, every row is a permutation of
$\{0, 1, \dots, n-1\}$, and in every column each value that occurs there occurs an even number
of times. -/
structure EvenTable (k n : ℕ) where
  entries : Fin k → Fin n → Fin n
  isEven : Even k
  rowBijective : ∀ i, Function.Bijective (entries i)
  colEven : ∀ (j : Fin n) (v : Fin n), (∃ i, entries i j = v) →
    Even ((List.ofFn fun i => entries i j).count v)

/-- **Weight of an even table.** Let $M$ be a commutative monoid and $f : \mathbb{N} \to M$. The
weight of an even $k \times n$ table $t$ with respect to $f$ is the product of the column weights
of its $n$ columns with respect to $f$:
$$\prod_{j=0}^{n-1} \prod_{v=0}^{n-1} f(m_j(v)),$$
where $m_j(v)$ is the number of times the value $v$ occurs in column $j$ of $t$. -/
def evenTableWeight {M : Type*} [CommMonoid M] {k n : ℕ}
    (factor : ℕ → M) (t : EvenTable k n) : M :=
  ∏ j, columnWeight n factor (List.ofFn fun i => t.entries i j)

end

end MetaMathlibExt
