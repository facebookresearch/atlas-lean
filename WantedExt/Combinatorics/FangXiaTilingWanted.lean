/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fang–Xia: tiling of the symmetric group by transpositions implies λ-transitivity

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.FangXiaTiling` — fang_xia_tiling_partition_transitive (manifest `manifests/problems/fang_xia_tiling_partition_transitive.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.FangXiaTilingWanted` namespace. Mathematical
statements are unchanged. Source: T. Fang and B. Xia, 'Tiling the symmetric group by transpositions', Bull. London Math. Soc. 58(5) (2026); DOI 10.1112/blms.70366; arXiv:2506.00360. The λ-transitivity notion in the statement is due to Martin–Sagan.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Combinatorics.FangXiaTilingWanted
namespace Combinatorics
namespace FangXiaTilingProblem

/-!
# Fang–Xia: tiling of the symmetric group by transpositions

If `T_n = {1} ∪ {all transpositions}` and `(T_n, Y)` is a tiling of the
symmetric group `S_n` (every element of `S_n` has a unique factorisation
`x · y` with `x ∈ T_n`, `y ∈ Y`), then every integer partition `λ` of
`n` whose Young-diagram content sum is nonnegative forces `Y` to be
**λ-transitive** in the Martin–Sagan sense: every pair of ordered set
partitions of shape `λ` is connected by exactly a fixed positive number
of permutations in `Y`. Fang–Xia, *Tiling the symmetric group by
transpositions*, Bull. London Math. Soc. **58**(5) (2026); DOI
`10.1112/blms.70366`; arXiv:2506.00360.
-/

open scoped BigOperators

/-- **Tiling of a group by two subsets.** For subsets $X$ and $Y$ of a group $G$, the pair
$(X, Y)$ is a tiling (or factorisation) of $G$ if every $g \in G$ can be written as $g = xy$
with $x \in X$ and $y \in Y$ for exactly one pair $(x, y)$. -/
def IsTiling {G : Type*} [Group G] (X Y : Set G) : Prop :=
  ∀ g : G, ∃! p : X × Y, (p.1 : G) * (p.2 : G) = g

/-- **The identity and the transpositions.** $T_n$ is the set of permutations of
$\{0, \dots, n-1\}$ consisting of the identity and all transpositions $(i\ j)$ with $i \ne j$. -/
def transpositionsWithOne (n : ℕ) : Set (Equiv.Perm (Fin n)) :=
  {σ | σ = 1 ∨ ∃ i j : Fin n, i ≠ j ∧ σ = Equiv.swap i j}

/-- **Integer partition as a list of row lengths.** A partition of $n$ is encoded as a list
$(\lambda_0, \lambda_1, \dots, \lambda_{k-1})$ of positive integers with
$\lambda_0 \ge \lambda_1 \ge \dots \ge \lambda_{k-1}$ and $\lambda_0 + \dots + \lambda_{k-1} = n$;
the $\lambda_i$ are its row lengths. -/
structure PartitionShape (n : ℕ) where
  parts : List ℕ
  sorted : parts.Pairwise (· ≥ ·)
  positive : ∀ a ∈ parts, 0 < a
  sum_eq : parts.sum = n

namespace PartitionShape

/-- **Shifted row-length sum.** For a natural number $i$ and a list of natural numbers
$a_0, \dots, a_{k-1}$, this is the integer $\sum_{j=0}^{k-1} a_j\,(a_j - 2(i + j) - 1)$; the
empty list gives $0$.

With $i = 0$ and the row lengths of a partition, this is twice the content sum of the partition. -/
def contentSumAux : ℕ → List ℕ → ℤ
  | _, [] => 0
  | i, a :: as => (a : ℤ) * ((a : ℤ) - 2 * (i : ℤ) - 1) + contentSumAux (i + 1) as

/-- **Twice the content sum of a partition.** For a partition $\lambda$ of $n$ with row lengths
$\lambda_0 \ge \lambda_1 \ge \dots \ge \lambda_{k-1}$, this is the integer
$\sum_{i=0}^{k-1} \lambda_i\,(\lambda_i - 2i - 1)$.

This is twice the content sum $\sum_{(i,j) \in \lambda} (j - i)$ of the Young diagram of
$\lambda$ (rows $i$ and columns $j$ counted from $0$), so it is nonnegative exactly when the
content sum is. It is the row-length formula from the remark after Theorem 1.4 of Fang–Xia,
whose one-indexed terms are $\lambda_i\,(\lambda_i - 2i + 1)$. -/
def contentSum {n : ℕ} (lam : PartitionShape n) : ℤ :=
  contentSumAux 0 lam.parts

end PartitionShape

/-- **Ordered set partition of shape λ.** Let $\lambda$ be a partition of $n$ with row lengths
$\lambda_0 \ge \dots \ge \lambda_{k-1}$. An ordered set partition of $\{0, \dots, n-1\}$ of shape
$\lambda$ is a sequence $(B_0, \dots, B_{k-1})$ of pairwise disjoint subsets of
$\{0, \dots, n-1\}$ whose union is $\{0, \dots, n-1\}$ and with $|B_i| = \lambda_i$ for every
$i$. -/
structure OrderedSetPartition {n : ℕ} (lam : PartitionShape n) where
  block : Fin lam.parts.length → Finset (Fin n)
  card_block : ∀ i : Fin lam.parts.length, (block i).card = lam.parts.get i
  pairwise_disjoint :
    Pairwise fun i j : Fin lam.parts.length => Disjoint (block i) (block j)
  union_eq_univ : (Finset.univ.biUnion block) = Finset.univ

/-- **Permutation sending one ordered set partition to another.** Let $\lambda$ be a partition
of $n$ and let $P = (P_0, \dots, P_{k-1})$ and $Q = (Q_0, \dots, Q_{k-1})$ be ordered set
partitions of $\{0, \dots, n-1\}$ of shape $\lambda$. A permutation $\sigma$ of
$\{0, \dots, n-1\}$ sends $P$ to $Q$ if $\sigma(P_i) = Q_i$ for every $i$. -/
def SendsPartition {n : ℕ} (σ : Equiv.Perm (Fin n)) {lam : PartitionShape n}
    (P Q : OrderedSetPartition lam) : Prop :=
  ∀ i : Fin lam.parts.length, (P.block i).image σ = Q.block i

/-- **λ-transitive sets of permutations.** Let $\lambda$ be a partition of $n$ with row lengths
$\lambda_0 \ge \dots \ge \lambda_{k-1}$. A set $Y$ of permutations of $\{0, \dots, n-1\}$ is
$\lambda$-transitive, in the sense of Martin and Sagan, if there is a positive integer $r$ such
that for any two ordered set partitions $P = (P_0, \dots, P_{k-1})$ and
$Q = (Q_0, \dots, Q_{k-1})$ of $\{0, \dots, n-1\}$ of shape $\lambda$, exactly $r$ permutations
$\sigma \in Y$ satisfy $\sigma(P_i) = Q_i$ for every $i$. -/
def IsPartitionTransitive {n : ℕ} (Y : Set (Equiv.Perm (Fin n)))
    (lam : PartitionShape n) : Prop :=
  ∃ r : ℕ, 0 < r ∧
    ∀ P Q : OrderedSetPartition lam,
      {σ : Equiv.Perm (Fin n) | σ ∈ Y ∧ SendsPartition σ P Q}.ncard = r

/- **Fang–Xia, Theorem 1.4.** A tiling `(T_n, Y)` of `S_n` forces
λ-transitivity of `Y` for every partition `λ` of `n` whose Young-
diagram content sum is nonnegative. -/
/-- **Fang–Xia: tilings by transpositions and λ-transitivity.** Let $S_n$ be the symmetric group
on $\{0, \dots, n-1\}$, let $T_n \subseteq S_n$ consist of the identity and all transpositions,
and let $Y \subseteq S_n$ be such that $(T_n, Y)$ is a tiling of $S_n$: every $g \in S_n$ can be
written as $g = xy$ with $x \in T_n$ and $y \in Y$ for exactly one pair $(x, y)$. Let $\lambda$
be a partition of $n$ with row lengths $\lambda_0 \ge \dots \ge \lambda_{k-1}$ such that
$\sum_{i=0}^{k-1} \lambda_i\,(\lambda_i - 2i - 1) \ge 0$ (equivalently, the content sum of the
Young diagram of $\lambda$ is nonnegative). Then $Y$ is $\lambda$-transitive: there is a
positive integer $r$ such that for any two ordered set partitions $P = (P_0, \dots, P_{k-1})$
and $Q = (Q_0, \dots, Q_{k-1})$ of $\{0, \dots, n-1\}$ with $|P_i| = |Q_i| = \lambda_i$ for
every $i$, exactly $r$ permutations $\sigma \in Y$ satisfy $\sigma(P_i) = Q_i$ for every $i$.

Source: T. Fang and B. Xia, 'Tiling the symmetric group by transpositions', Bull. London Math. Soc. 58(5) (2026); DOI 10.1112/blms.70366; arXiv:2506.00360. The λ-transitivity notion in the statement is due to Martin–Sagan. Via leanprover/lean-eval@38361be, problem `fang_xia_tiling_partition_transitive`. -/
public theorem_wanted fang_xia_partition_transitive_of_tiling
    {n : ℕ} {Y : Set (Equiv.Perm (Fin n))}
    (_h : IsTiling (transpositionsWithOne n) Y) :
    ∀ lam : PartitionShape n, 0 ≤ lam.contentSum → IsPartitionTransitive Y lam

end FangXiaTilingProblem
end Combinatorics

end MathlibExt.Combinatorics.FangXiaTilingWanted
