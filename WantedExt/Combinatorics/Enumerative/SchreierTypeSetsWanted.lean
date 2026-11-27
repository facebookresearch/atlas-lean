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
is the source used for the definitions below.

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
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.RefinedSchreierMinimum
public import MathlibExt.Combinatorics.Enumerative.SchreierSparseCount
public import MathlibExt.Combinatorics.Enumerative.StrongSchreierCount

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted

/-- **Strongly sparse sets.** A finite set of natural numbers is *strongly sparse* if the
differences between consecutive elements in increasing order are strictly increasing. -/
def IsStronglySparse (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < b → b < c →
    (∀ x ∈ A, a < x → b ≤ x) → (∀ x ∈ A, b < x → c ≤ x) →
      b - a < c - b

instance (A : Finset ℕ) : Decidable (IsStronglySparse A) := by
  unfold IsStronglySparse; infer_instance

/-- **Partitions into exactly $k$ parts.** For natural numbers $u$ and $k$, $p(u, k)$ is the
number of partitions of $u$ into exactly $k$ parts. -/
def partitionExactCount (u k : ℕ) : ℕ :=
  (Finset.univ.filter (fun P : Nat.Partition u =>
    P.parts.card = k)).card

/-- **Number of Schreier sparse sets with given minimum and maximum.** For natural numbers $n$
and $m$, $|F_{n,m}|$ is the number of sets $F \subseteq \{1, \dots, n\}$ that are Schreier and
sparse, contain $n$, and have minimum $m$. -/
def schreierSparseMinCount (n m : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun F => IsSchreier F ∧
    IsSparse F ∧ n ∈ F ∧ m ∈ F ∧ ∀ a ∈ F, m ≤ a)).card

/-- **Number of sparse strong Schreier sets with maximum $n$.** For natural numbers $n$ and
$\ell$, $|A_{n,\ell}|$ is the number of sets $A \subseteq \{1, \dots, n\}$ with $n \in A$ that
are sparse and $\ell$-strong Schreier. -/
def sparseStrongCount (n l : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun A => n ∈ A ∧
    IsSparse A ∧ IsStrongSchreier l A)).card

/-- **Number of strongly sparse strong Schreier sets with a given maximum.** For natural numbers
$n$ and $\ell$, $|A^s_{n,\ell}|$ is the number of sets $A \subseteq \{1, \dots, n\}$ with $n \in A$
that are strongly sparse, meaning that the differences between consecutive elements of $A$ in
increasing order are strictly increasing, and $\ell$-strong Schreier, meaning that every element
of $A$ is at least $\ell|A| - \ell + 1$. -/
def stronglySparseStrongCount (n l : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun A => n ∈ A ∧
    IsStronglySparse A ∧ IsStrongSchreier l A)).card

/-- **Number of strong Schreier sets of given size with maximum $n$.** For natural numbers $n$,
$\ell$ and $m$, $|B_{n,\ell,m}|$ is the number of $\ell$-strong Schreier sets
$B \subseteq \{1, \dots, n\}$ with $n \in B$ and exactly $m$ elements. -/
def strongSchreierCardCount (n l m : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun B => n ∈ B ∧
    B.card = m ∧ IsStrongSchreier l B)).card

/-- **Partitions into distinct parts at least $\ell$.** For natural numbers $n$ and $\ell$, let
$E^d_{n,\ell}$ be the set of partitions of $n$ into pairwise distinct parts, each at least
$\ell$. This is its number of elements $|E^d_{n,\ell}|$. -/
def partitionDistinctMinPartCount (n l : ℕ) : ℕ :=
  (Nat.Partition.restricted n (fun x => l ≤ x) ∩
    Nat.Partition.distincts n).card

/-- **Partitions avoiding parts from 2 up to a bound.** For natural numbers $n$ and $\ell$,
$|G_{n,\ell}|$ is the number of partitions of $n$ none of whose parts lies in
$\{2, \dots, \ell\}$. -/
def partitionNoSmallPartCount (n l : ℕ) : ℕ :=
  (Nat.Partition.restricted n (fun x => ¬ (2 ≤ x ∧ x ≤ l))).card

/-- **Partitions avoiding parts from 2 up to a bound and large even parts.** For natural numbers
$n$ and $\ell$, $|H_{n,\ell}|$ is the number of partitions of $n$ none of whose parts lies in
$\{2, \dots, \ell\}$ and none of whose parts is an even number greater than $2\ell$. -/
def partitionNoSmallNoEvenCount (n l : ℕ) : ℕ :=
  (Nat.Partition.restricted n
    (fun x => ¬ (2 ≤ x ∧ x ≤ l) ∧ (Even x → x ≤ 2 * l))).card

/-- **Compositions with exactly $s$ parts, each at least $v$.** For natural numbers $u$, $v$
and $s$, $c(u, v, s)$ is the number of compositions of $u$ (ordered sequences of positive
integers summing to $u$) into exactly $s$ parts, each at least $v$. -/
def compositionMinPartExactCount (u v s : ℕ) : ℕ :=
  Fintype.card {c : Composition u //
    (∀ x ∈ c.blocks, v ≤ x) ∧ c.length = s}

/-- **Schreier sparse sets with given minimum and maximum.** For natural numbers $m$ and $n$
with $m + 1 \le n$, the number of Schreier sparse sets $F \subseteq \{1, \dots, n\}$ with
$n \in F$ and $\min F = m + 1$ equals $p(n - 1, m)$, the number of partitions of $n - 1$ into
exactly $m$ parts.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Proposition 2. -/
theorem_wanted schreierSparseMinCount_eq (m n : ℕ) (hmn : m + 1 ≤ n) :
    schreierSparseMinCount n (m + 1) = partitionExactCount (n - 1) m

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

end MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted
