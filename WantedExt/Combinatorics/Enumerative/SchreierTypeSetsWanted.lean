/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On Schreier-type sets, partitions, and compositions

Statements from Kevin Beanland and Hùng Việt Chu, "On
Schreier-Type Sets, Partitions, and Compositions", *Journal of
Integer Sequences* 27 (2024), Article 24.4.4
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Beanland/bean4.html>).
The publisher TeX at
<https://cs.uwaterloo.ca/journals/JIS/VOL27/Beanland/bean4.tex>
is the source for the definitions in the imported Schreier-type sets module.

A finite set `A` of positive integers is *Schreier* if it is empty
or `min A ≥ |A|`, and *`ℓ`-strong Schreier* if it is empty or
`min A ≥ ℓ|A| - ℓ + 1`; both are encoded here by the equivalent
conditions on all elements of `A`, which are vacuous for `A = ∅`.
A set is *sparse* if the differences between consecutive elements
(in increasing order) are non-decreasing, and *strongly sparse*
if they are strictly increasing; both are encoded by quantifying
over consecutive triples, which is vacuous for `|A| ≤ 2`, as in
the paper.

Partitions are Mathlib's `Nat.Partition`, with `P.parts` the
multiset of parts.  The paper's conventions `|E_{0,ℓ}| = 1` etc.
are automatic since `Nat.Partition 0` has the single empty
partition.  Compositions are Mathlib's `Composition u`, with
parts at least `v` imposed on `c.blocks` and exactly `s` parts
as `c.length = s`.

Parameter ranges follow the paper (whose `ℕ` is the positive
integers): Theorem 6 allows `ℓ ≥ 0` explicitly, Theorem 9 allows
`ℓ ≥ 0` but quantifies `m, n ∈ ℕ` (so `1 ≤ m` is a hypothesis
below), and the Section 4 setup chooses `n ≥ 1` and `ℓ ≥ 0`, so
`ℓ = 0` in Theorems 6 and 9 and in Lemma 11/Corollaries 12-13
is paper domain, not an extension.  Theorem 7 is quantified over
`1 ≤ n` and `1 ≤ ℓ`: the paper quantifies over `n, ℓ ∈ ℕ`, and
the identities fail at `ℓ = 0` (for example
`|A_{2,0}| = 2 ≠ 1 = |G_{1,0}|`).  Partition counts are defined
through Mathlib's `Nat.Partition.restricted` and
`Nat.Partition.distincts`; set-family counts are filtered
powersets; composition counts use Mathlib's `Composition u`
(positive block sizes), which agrees with the paper's `c(u, v)`
and `c(u, v, s)` at the values `v = ℓ + 1 ≥ 1` used in
Theorem 9.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Combinatorics.Enumerative.SchreierTypeSets

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted

/-- **Schreier sparse sets with given minimum and maximum.** For natural numbers $m$ and $n$
with $m + 1 \le n$, the number of Schreier sparse sets $F \subseteq \{1, \dots, n\}$ with
$n \in F$ and $\min F = m + 1$ equals $p(n - 1, m)$, the number of partitions of $n - 1$ into
exactly $m$ parts.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Proposition 2. -/
theorem_wanted schreierSparseMinCount_eq (m n : ℕ) (hmn : m + 1 ≤ n) :
    schreierSparseMinCount n (m + 1) = partitionExactCount (n - 1) m

/-- **Counting Schreier sparse sets by partition numbers.** For every integer $n \ge 1$, the
number of Schreier sparse sets $F \subseteq \{1, \dots, n\}$ with $n \in F$ equals $p(n - 1)$,
the number of partitions of $n - 1$.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Corollary 3. -/
theorem_wanted schreierSparseCount_eq (n : ℕ) (hn : 1 ≤ n) :
    schreierSparseCount n = partitionCount (n - 1)

/-- **Sparse strong Schreier sets as a sum of partition counts.** For every integer $n \ge 1$
and every natural number $\ell$, the number of sparse $\ell$-strong Schreier sets
$A \subseteq \{1, \dots, n\}$ with $n \in A$ equals $\sum_{i=0}^{n-1} |E_{i,\ell+1}|$, where
$|E_{i,\ell+1}|$ is the number of partitions of $i$ into parts that are all at least $\ell + 1$.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Theorem 6. -/
theorem_wanted sparseStrongCount_eq_sum (n l : ℕ) (hn : 1 ≤ n) :
    sparseStrongCount n l =
      ∑ i ∈ Finset.range n, partitionMinPartCount i (l + 1)

/-- **Strongly sparse strong Schreier sets and partitions into distinct parts.** For all natural
numbers $n \ge 1$ and $\ell \ge 0$, the number $|A^s_{n,\ell}|$ of strongly sparse $\ell$-strong
Schreier sets $A \subseteq \{1, \dots, n\}$ with $n \in A$ equals
$\sum_{i=0}^{n-1} |E^d_{i,\ell+1}|$, where $|E^d_{i,\ell+1}|$ is the number of partitions of $i$
into distinct parts that are all at least $\ell + 1$ (so $|E^d_{0,\ell+1}| = 1$). Here $A$ is
strongly sparse when the differences between consecutive elements of $A$, listed in increasing
order, are strictly increasing, and $\ell$-strong Schreier when every element of $A$ is at least
$\ell|A| - \ell + 1$.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Theorem 6. -/
theorem_wanted stronglySparseStrongCount_eq_sum (n l : ℕ)
    (hn : 1 ≤ n) :
    stronglySparseStrongCount n l =
      ∑ i ∈ Finset.range n, partitionDistinctMinPartCount i (l + 1)

/-- **Sparse strong Schreier sets and partitions avoiding small parts.** For all integers
$n \ge 1$ and $\ell \ge 1$, the number of sparse $\ell$-strong Schreier sets
$A \subseteq \{1, \dots, n\}$ with $n \in A$ equals the number of partitions of $n - 1$ with no
part in $\{2, \dots, \ell\}$.

The identity fails at $\ell = 0$; the paper's $\mathbb{N}$ is the positive integers.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Theorem 7. -/
theorem_wanted sparseStrongCount_eq_noSmall (n l : ℕ) (hn : 1 ≤ n)
    (hl : 1 ≤ l) :
    sparseStrongCount n l = partitionNoSmallPartCount (n - 1) l

/-- **Strongly sparse strong Schreier sets and partitions with restricted parts.** For all natural
numbers $n \ge 1$ and $\ell \ge 1$, the number $|A^s_{n,\ell}|$ of strongly sparse $\ell$-strong
Schreier sets $A \subseteq \{1, \dots, n\}$ with $n \in A$ equals $|H_{n-1,\ell}|$, the number of
partitions of $n - 1$ with no part in $\{2, \dots, \ell\}$ and no even part greater than $2\ell$.
Here $A$ is strongly sparse when the differences between consecutive elements of $A$, listed in
increasing order, are strictly increasing, and $\ell$-strong Schreier when every element of $A$ is
at least $\ell|A| - \ell + 1$.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Theorem 7. -/
theorem_wanted stronglySparseStrongCount_eq_noSmallNoEven (n l : ℕ)
    (hn : 1 ≤ n) (hl : 1 ≤ l) :
    stronglySparseStrongCount n l =
      partitionNoSmallNoEvenCount (n - 1) l

/-- **Strong Schreier sets of given size and compositions.** For all integers $n \ge 1$ and
$m \ge 1$ and every natural number $\ell$, the number of $\ell$-strong Schreier sets
$B \subseteq \{1, \dots, n\}$ with $n \in B$ and exactly $m$ elements equals the number of
compositions of $n + \ell$ into exactly $m$ parts, each at least $\ell + 1$.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Theorem 9. -/
theorem_wanted strongSchreierCardCount_eq (m n l : ℕ) (hn : 1 ≤ n)
    (hm : 1 ≤ m) :
    strongSchreierCardCount n l m =
      compositionMinPartExactCount (n + l) (l + 1) m

/-- **Strong Schreier sets with a given maximum are counted by compositions.** For all natural
numbers $n \ge 1$ and $\ell \ge 0$, the number $|B_{n,\ell}|$ of $\ell$-strong Schreier sets
$B \subseteq \{1, \dots, n\}$ with $n \in B$ equals $c(n + \ell, \ell + 1)$, the number of
compositions of $n + \ell$ into parts that are all at least $\ell + 1$. Here a set $B$ is
$\ell$-strong Schreier when every element of $B$ is at least $\ell|B| - \ell + 1$.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Theorem 9. -/
theorem_wanted strongSchreierCount_eq (n l : ℕ) (hn : 1 ≤ n) :
    strongSchreierCount n l = compositionMinPartCount (n + l) (l + 1)

/-- **Refined Schreier sets with a given minimum and partitions with a given top gap.** Let
$n$, $\ell$, $k$ and $q$ be natural numbers with $n \ge \ell + 1$, $k \ge 2$ and $q \ge 1$.
Let $F_{n,\ell}$ be the family of finite sets $A$ of natural numbers such that $A$ has largest
element $n + 1$ and at least three elements, $A$ is sparse (the differences of consecutive
elements, in increasing order, are non-decreasing) and $\ell$-strong Schreier
($\ell|A| + 1 \le a + \ell$ for every $a \in A$), and the second and third largest elements
$b > a$ of $A$ satisfy $n + 1 + a = 2b$. Then the number $|F_{n,\ell,k+1,\ell k+q}|$ of sets
in $F_{n,\ell}$ with exactly $k + 1$ elements and smallest element $\ell k + q$ equals the
number $|E_{n,\ell+1,k,q-1}|$ of partitions of $n$ into exactly $k$ parts, all at least
$\ell + 1$, whose largest part exceeds the second largest part (counted with multiplicity) by
exactly $q - 1$.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Lemma 11. -/
theorem_wanted refinedSchreierCardMinCount_eq (n l k q : ℕ)
    (hn : l + 1 ≤ n) (hk : 2 ≤ k) (hq : 1 ≤ q) :
    refinedSchreierCardMinCount n l (k + 1) (l * k + q) =
      partitionMinPartGapCount n (l + 1) k (q - 1)

/-- **Partitions with a fixed number of large parts and refined Schreier sets.** Let $n$,
$\ell$ and $k$ be natural numbers with $n \ge \ell + 1$ and $k \ge 2$. Let $F_{n,\ell}$ be the
family of finite sets $A$ of natural numbers such that $A$ has largest element $n + 1$ and at
least three elements, $A$ is sparse (the differences of consecutive elements, in increasing
order, are non-decreasing) and $\ell$-strong Schreier ($\ell|A| + 1 \le a + \ell$ for every
$a \in A$), and the second and third largest elements $b > a$ of $A$ satisfy
$n + 1 + a = 2b$. Then the number $|E_{n,\ell+1,k}|$ of partitions of $n$ into exactly $k$
parts, all at least $\ell + 1$, equals the number $|F_{n,\ell,k+1}|$ of sets in $F_{n,\ell}$
with exactly $k + 1$ elements.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Corollary 12. -/
theorem_wanted partitionMinPartExactCount_eq_refined (n l k : ℕ)
    (hn : l + 1 ≤ n) (hk : 2 ≤ k) :
    partitionMinPartExactCount n (l + 1) k =
      refinedSchreierCardCount n l (k + 1)

end MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted
