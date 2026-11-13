/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Mark Sepanski
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Tactic.IntervalCases

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 27, Combinatorics 28, Combinatorics 444, Combinatorics 445, Combinatorics 452, Combinatorics 460, Combinatorics 461, Combinatorics 489

/-!
# `MathlibExt.Combinatorics.Fundamentals.Partitions`

## References

* ec1 p 25 (for `WeakComposition`)
* ec1 p 45 (for `SetComposition`)
* ec1 1.8.3 (for `List.partitionConjugate`, `List.IsSelfConjugate`)
* ec1 1.7.3 (for `Nat.partitionsInBox`)
* ec1 2.5.1 (for `Nat.VPartition`)
* ec1 2.5.2 (for `List.IsUnimodal`)
* ec2 7.2 p 288 (for `Nat.Partition.Dominates`)
-/

namespace MetaMathlibExt

-- Combinatorics 27: Weak Composition

/-- Let n,k∈ℕ. A weak composition of n into
k parts is a function

  a:{i∈ℕ∣ i<k}→ℕ

such that

  ∑ᵢ₌₀ᵏ⁻¹a(i)=n.

The values a(i) are called the parts and may be zero.
When k=0, the empty function is a weak composition
exactly when n=0.
-/
def WeakComposition (n k : ℕ) :=
  { a : Fin k → ℕ //
    (Finset.univ : Finset (Fin k)).sum a = n
  }

-- Combinatorics 28: Ordered Set Partition

/-- Let S be a finite set and let k∈ℕ. An
ordered set partition of S into k blocks is an ordered
tuple

  (B₁,…,Bₖ)

of subsets of S such that

  Bᵢ≠∅ (1≤ i≤ k),

  Bᵢ∩ Bⱼ=∅
   (1≤ i,j≤ k, i≠ j),

and

  ⋃ᵢ₌₁ᵏ Bᵢ=S.

When k=0, the empty tuple is an ordered set partition
exactly when S=∅.
-/
def SetComposition {α : Type*} [DecidableEq α]
    (S : Finset α) (k : ℕ) :=
  { B : Fin k → Finset α //
    (∀ i, (B i).Nonempty) ∧
    (∀ i j, i ≠ j →
      Disjoint (B i) (B j)) ∧
    ((Finset.univ : Finset (Fin k)).biUnion B = S)
  }

-- Combinatorics 444: Conjugate Partition


/-- **Conjugate partition.** Let $\lambda = [\lambda_1, \dots, \lambda_L]$ be a finite list of
natural numbers, with $L \ge 0$. Its conjugate $\lambda'$ is the empty list if $L = 0$, and
otherwise the list $[\lambda'_1, \dots, \lambda'_{\lambda_1}]$ of length $\lambda_1$ with
$\lambda'_j = \#\{i : 1 \le i \le L,\ \lambda_i \ge j\}$ for $1 \le j \le \lambda_1$. The length
is set by the first entry $\lambda_1$, and the entries of $\lambda'$ are weakly decreasing and at
least $1$.

When $\lambda$ is a partition, $\lambda_1 \ge \dots \ge \lambda_L \ge 1$, its first entry is its
largest part, and $\lambda'$ is the conjugate partition: its Young diagram is the transpose of the
Young diagram of $\lambda$.
-/
def _root_.List.partitionConjugate (l : List ℕ) : List ℕ :=
  (List.range (l.head?.getD 0)).map fun j =>
    (l.filter fun p => decide (j + 1 ≤ p)).length

-- Combinatorics 445: Self-Conjugate Partition


/-- **Self-conjugate partition.** Let $\lambda = [\lambda_1, \dots, \lambda_L]$ be a finite list of
natural numbers, with $L \ge 0$. Its conjugate $\lambda'$ is the empty list if $L = 0$, and
otherwise the list $[\lambda'_1, \dots, \lambda'_{\lambda_1}]$ of length $\lambda_1$ with
$\lambda'_j = \#\{i : 1 \le i \le L,\ \lambda_i \ge j\}$ for $1 \le j \le \lambda_1$. The list
$\lambda$ is self-conjugate when $\lambda' = \lambda$.

The conjugate of any list is weakly decreasing with all entries at least $1$, so a self-conjugate
list is a partition $\lambda_1 \ge \dots \ge \lambda_L \ge 1$, and for a partition the condition
says that its Young diagram equals its own transpose. The empty list is self-conjugate.
-/
def List.IsSelfConjugate (l : List ℕ) : Prop :=
  l.partitionConjugate = l

-- Combinatorics 452: Partitions in a Box


/-- **Number of partitions in a box.** Let $j, k, n \ge 0$ be integers. A partition of $n$ is a
finite multiset of positive integers whose sum is $n$; the empty partition is the unique partition
of $0$. Then $p(j, k, n)$ is the number of partitions of $n$ with at most $k$ parts, counted with
multiplicity, each of which is at most $j$. In particular $p(j, k, 0) = 1$ for all $j$ and $k$,
while $p(0, k, n) = p(j, 0, n) = 0$ for $n \ge 1$.
-/
def Nat.partitionsInBox (j k n : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Nat.Partition n =>
    Multiset.card p.parts ≤ k ∧
      ∀ x ∈ p.parts, x ≤ j).card

-- Combinatorics 460: V-Partition


/-! ### Informal statement of `Nat.VPartition`

Let n∈ℤ_{≥ 0}. A partition is
a finite multiset of positive integers, and
its weight |λ| is the sum
of its parts. Written in weakly decreasing
order a partition is
λ=[λ₁,…,λₘ] with
λ₁≥⋯≥λₘ≥ 1; for
m=0 it is the empty partition
∅, of weight 0.

A V-partition of weight n is a triple
(c,λ,μ) in which
c∈ℤ_{≥ 0}, both λ and
μ are partitions all of whose parts are
at most c, and

  c+|λ|+|μ|=n.

The name comes from the shape of the array
in which c sits at the vertex, λ is
written along the upper arm and μ along
the lower one, with trailing zero entries
omitted. The two arms are ordered, so
(c,λ,μ) and (c,μ,λ) are
distinct whenever λ≠μ.

No separate bound on c is needed, since
c, |λ| and
|μ| are nonnegative with sum
n, whence c≤ n. If c=0 then every
part of λ and of μ is a positive
integer at most 0, so both are empty and
n=0. Hence (0,∅,∅) is
the unique V-partition of weight 0.
Writing v(n) for the number of
V-partitions of weight n, this gives
v(0)=1, and the next values are v(1)=1,
v(2)=3, v(3)=6 and v(4)=12.
-/

/-- **V-partition.** Let $n \ge 0$ be an integer. A partition $\lambda$ is a finite multiset of
positive integers, and its weight $|\lambda|$ is the sum of its parts. A V-partition of weight $n$
is a triple $(c, \lambda, \mu)$ in which $c \ge 0$ is an integer, $\lambda$ and $\mu$ are
partitions all of whose parts are at most $c$, and $c + |\lambda| + |\mu| = n$.

The order of $\lambda$ and $\mu$ matters, so $(c, \lambda, \mu)$ and $(c, \mu, \lambda)$ are
distinct whenever $\lambda \ne \mu$.
-/
structure Nat.VPartition (n : ℕ) where
  corner : ℕ
  left : Multiset ℕ
  right : Multiset ℕ
  left_pos : ∀ x ∈ left, 0 < x
  right_pos : ∀ x ∈ right, 0 < x
  left_le : ∀ x ∈ left, x ≤ corner
  right_le : ∀ x ∈ right, x ≤ corner
  weight : corner + left.sum + right.sum = n

-- Combinatorics 461: Unimodal Sequence


/-! ### Informal statement of `List.IsUnimodal`

Let m∈ℤ_{≥ 1} and write
[m]={1,…,m}. A unimodal sequence is
a nonempty list d=[d₁,…,dₘ] of
integers with dᵢ≥ 1 for
1≤ i≤ m, for which there is a peak
index j∈[m] with

  dᵢ≤ dᵢ₊₁ (1≤ i<j),

  dᵢ≥ dᵢ₊₁ (j≤ i<m),

that is, with

  d₁≤⋯≤ dⱼ
   and
  dⱼ≥⋯≥ dₘ.

The term dⱼ lies in both runs and is the
largest, so dᵢ≤ dⱼ for every i with
1≤ i≤ m. Either range of i may be
empty: for j=1 the first condition is
vacuous and d is weakly decreasing, and
for j=m the second is vacuous and d is
weakly increasing. For m=1 the one-term
list [d₁] is unimodal. The empty list is
not unimodal. The inequalities are weak, so
a plateau is allowed and any index inside a
plateau may serve as j; the index j is
part of the condition and not part of the
object.

The weight of d is

  | d|=∑ᵢ₌₁ᵐdᵢ,

and u(n) denotes the number of unimodal
sequences of weight n. Every unimodal
sequence has at least one term and every
term is at least 1, so its weight is at
least 1 and u(0)=0. The next values are
u(1)=1, u(2)=2, u(3)=4, u(4)=8 and
u(5)=15.

The Lean indexes positions from 0, so the
peak index there is j-1.
-/

/-- **Unimodal sequence.** A finite list $d = [d_1, \dots, d_m]$ of natural numbers is unimodal
when $d_i \ge 1$ for every $i$ and there is an index $j$ with $1 \le j \le m$ such that
$d_1 \le d_2 \le \dots \le d_j$ and $d_j \ge d_{j+1} \ge \dots \ge d_m$. In particular a unimodal
list has $m \ge 1$, so the empty list is not unimodal; for $j = 1$ the first condition is vacuous
and for $j = m$ the second is.
-/
def List.IsUnimodal (d : List ℕ) : Prop :=
  (∀ x ∈ d, 0 < x) ∧
    ∃ j < d.length,
      (d.take (j + 1)).Pairwise (· ≤ ·) ∧
        (d.drop j).Pairwise (· ≥ ·)

-- Combinatorics 489: Dominance Order


/-- **Dominance order on partitions.** Let $n \ge 0$ be an integer. A partition of $n$ is a finite
multiset of positive integers with sum $n$; write it as the list
$\lambda = [\lambda_1, \dots, \lambda_m]$ of its parts in weakly decreasing order, so that
$\lambda_1 \ge \dots \ge \lambda_m \ge 1$ and $\lambda_1 + \dots + \lambda_m = n$, and set
$\lambda_j = 0$ for every integer $j > m$. The empty partition ($m = 0$) is the unique partition
of $0$. For partitions $\lambda$ and $\mu$ of $n$, $\lambda$ dominates $\mu$, written
$\mu \le \lambda$, if $\mu_1 + \dots + \mu_i \le \lambda_1 + \dots + \lambda_i$ for every integer
$i \ge 0$, where both sums are $0$ when $i = 0$.
-/
def _root_.Nat.Partition.Dominates {n : ℕ} (p q : n.Partition) : Prop :=
  ∀ i : ℕ, ((q.parts.sort (· ≥ ·)).take i).sum ≤
    ((p.parts.sort (· ≥ ·)).take i).sum

end MetaMathlibExt

end
