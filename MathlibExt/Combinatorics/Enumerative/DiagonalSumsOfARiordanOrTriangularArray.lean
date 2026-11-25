/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-- **Diagonal sums of an array.** For a doubly indexed array $(a_{i,j})_{i, j \ge 0}$ with entries
in an additive commutative monoid $M$, the $n$-th diagonal sum is
$d_n = \sum_{i + j = n} a_{i,j} = \sum_{k=0}^{n} a_{k,n-k}$.

If $a$ is a lower-triangular array with $a_{i,j}$ in row $i$ and column $j$, these are its sums
along rising diagonals. For a Riordan array $(g, f)$, whose column $j$ has generating function
$g(x) f(x)^j$, the sequence $(d_n)$ has generating function $g(x) / (1 - x f(x))$.

Sources: concept `jis_sem_c3bf1fb2d96732b9f14d51d2`
(`diagonal sums of a Riordan or triangular array`);
statements `jis_1fa1c63beb99b6d942ce3fe3`, `jis_4b608c30d02bc9d0bb18b1ad`,
`jis_509208625b436fe419d6aa27`, `jis_75a2bcc65150b23df74aa083`,
`jis_799c84fba972a9e02b813f68`, `jis_8ac1daf4464d5f9b03e74e04`,
`jis_9694b3ddf1cac31314a02552`, `jis_cde4fe6dab53c64bf1efc7ff`,
`jis_da460a82515493c122167fec`. -/
public def diagonalSums {M : Type*} [AddCommMonoid M] (a : ℕ → ℕ → M) (n : ℕ) : M :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, a ij.1 ij.2

end

end MetaMathlibExt
