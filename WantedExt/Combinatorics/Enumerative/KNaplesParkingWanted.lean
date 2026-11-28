/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.DescendingNaplesBinaryTrees
public import MathlibExt.Combinatorics.Enumerative.DescendingNaplesDyckPath
public import MathlibExt.Combinatorics.Enumerative.DescendingNaplesPaddedDyckWord
public import MathlibExt.Combinatorics.Enumerative.KNaplesParking
public import MathlibExt.Combinatorics.Enumerative.KNaplesParkingInt
public import MathlibExt.Combinatorics.FineNumber
public import MathlibExt.Combinatorics.NoncrossingPartition.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree

namespace MetaMathlibExt

@[expose] public section

/-- **A $2$-Naples parking example.** Under the $2$-Naples rule on the spots $1, \dots, 7$, the
cars with preferences $(6, 6, 6, 5, 5, 2, 1)$, arriving in order into an empty lot, all park, in
the spots $6, 5, 4, 3, 7, 2, 1$ respectively.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 1. -/
public theorem naplesPark_example :
    naplesPark 7 2 [] [6, 6, 6, 5, 5, 2, 1] = some [1, 2, 7, 3, 4, 5, 6] := by
  decide

/-- **A $2$-Naples parking function that is not $1$-Naples.** The preference
$(6, 6, 6, 5, 5, 2, 1)$ of length $7$ is a $2$-Naples parking function but not a $1$-Naples
parking function.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 1. -/
public theorem isNaplesParkingFunction_example :
    IsNaplesParkingFunction 2 ![6, 6, 6, 5, 5, 2, 1] ∧
      ¬ IsNaplesParkingFunction 1 ![6, 6, 6, 5, 5, 2, 1] := by
  decide

/-- **Number of ascending $k$-Naples parking functions.** For natural numbers $n$ and $k$,
$I_{n,k}$ is the number of $k$-Naples parking functions $(a_1, \dots, a_n)$ of length $n$ that
are weakly increasing, that is, $a_1 \le a_2 \le \dots \le a_n$.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 3. -/
public def ascendingNaplesCount (n k : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin n => Finset.Icc 1 n).filter fun α =>
    (∀ i j : Fin n, i ≤ j → α i ≤ α j) ∧ IsNaplesParkingFunction k α).card

/-- **Number of ascending $k$-Naples parking functions starting with $1$.** For natural numbers
$n$ and $k$, $U_{n,k}$ is the number of weakly increasing $k$-Naples parking functions
$(a_1, \dots, a_n)$ of length $n$ with $a_1 = 1$; in particular $U_{0,k} = 0$.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 3. -/
public def ascendingNaplesOneCount (n k : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin n => Finset.Icc 1 n).filter fun α =>
    (∀ i j : Fin n, i ≤ j → α i ≤ α j) ∧ IsNaplesParkingFunction k α ∧
      ∃ i : Fin n, i.val = 0 ∧ α i = 1).card

/-- **Naples counts for $n = 2$ and $k = 1$.** Among the preferences of length $2$ with entries
in $\{1, 2\}$, exactly $3$ are weakly increasing $1$-Naples parking functions ($I_{2,1} = 3$),
and exactly $2$ of these start with $1$ ($U_{2,1} = 2$); exactly $3$ are weakly decreasing
$1$-Naples parking functions, and exactly $1$ is weakly decreasing, $1$-Naples and not
$0$-Naples.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 4. -/
public theorem naplesCount_two_one :
    ascendingNaplesCount 2 1 = 3 ∧ ascendingNaplesOneCount 2 1 = 2 ∧
      descendingNaplesCount 2 1 = 3 ∧ descendingStrictNaplesCount 2 1 = 1 := by
  decide

/-- **A $1$-Dyck path that is not a $0$-Dyck path.** Write $U$ for an Up step $(1, 1)$ and $D$
for a Down step $(1, -1)$. The path $DUUD$ is a $1$-Dyck path of semilength $2$ but not a
$0$-Dyck path, and the path $UUD$ has height $1$ after its three steps.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 3. -/
public theorem isKDyckPath_example :
    IsKDyckPath 2 1 ![false, true, true, false] ∧ ¬ IsKDyckPath 2 0 ![false, true, true, false] ∧
      dyckStepHeight [DyckStep.U, DyckStep.U, DyckStep.D] 3 = 1 := by
  unfold IsKDyckPath latticeHeight dyckStepHeight
  decide

/-- **A $2$-Naples parking example on $\mathbb{Z}$.** Under the $2$-Naples rule on $\mathbb{Z}$,
the cars with preferences $(4, 2, 2, 2)$, arriving in order with no spot occupied, park in the
spots $4, 2, 1, 0$ respectively.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 2, Figure 1. -/
public theorem naplesParkInt_example :
    naplesParkInt 2 [] [4, 2, 2, 2] = [0, 1, 2, 4] := by
  decide

/-- **A $3$-Naples parking example on $\mathbb{Z}$.** Under the $3$-Naples rule on $\mathbb{Z}$,
the cars with preferences $(1, 2, 2, 5, 7, 7, 7, 3)$, arriving in order with no spot occupied,
park in the spots $1, 2, 0, 5, 7, 6, 4, 3$ respectively.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 2, Remark 2. -/
public theorem naplesParkInt_example_three :
    naplesParkInt 3 [] [1, 2, 2, 5, 7, 7, 7, 3] = [3, 4, 6, 7, 5, 0, 2, 1] := by
  decide

open Classical in
/-- **Descending strictly $k$-Naples parking functions and Dyck paths with an early return.**
For $n \ge 1$ and $k \ge 1$, the number of descending strictly $k$-Naples parking functions of
length $n$ (descending preferences that are $k$-Naples but not $(k - 1)$-Naples) equals the
number of Dyck paths of semilength $n + k$, that is, with $2(n + k)$ Up and Down steps, whose
first $k$ steps are Up, whose last $k + 1$ steps are Down, and whose height after $j$ steps is
$0$ for some $j$ with $0 < j < 2(n + k)$.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Proposition 4. -/
public theorem_wanted descendingStrictNaplesCount_eq_card_dyckPath {n k : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) :
    descendingStrictNaplesCount n k = (Finset.univ.filter
      fun p : {p : DyckWord // p.semilength = n + k} =>
        List.replicate k DyckStep.U <+: p.1.toList ∧
          List.replicate (k + 1) DyckStep.D <:+ p.1.toList ∧
          ∃ j < 2 * (n + k), 0 < j ∧ dyckStepHeight p.1.toList j = 0).card

/-- **Recurrence for ascending $k$-Naples parking functions.** Let $I_{n,k}$ be the number of
weakly increasing $k$-Naples parking functions of length $n$, let $U_{n,k}$ be the number of
those whose first entry is $1$, and let $C_k$ be the $k$-th Catalan number. For all natural
numbers $n$ and $k$ with $1 \le k \le n - 1$,
$$I_{n,k} = I_{n,k-1} + C_k \sum_{i=0}^{n-k} I_{i,k-1} \, U_{n-k-i,k}$$
and
$$U_{n,k} = U_{n,k-1} + C_k \sum_{i=0}^{n-k} U_{i,k-1} \, U_{n-k-i,k}.$$

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 3. -/
public theorem_wanted ascendingNaplesCount_recurrence {n k : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    ascendingNaplesCount n k = ascendingNaplesCount n (k - 1) + catalan k *
        ∑ i ∈ Finset.range (n - k + 1),
          ascendingNaplesCount i (k - 1) * ascendingNaplesOneCount (n - k - i) k ∧
      ascendingNaplesOneCount n k = ascendingNaplesOneCount n (k - 1) + catalan k *
        ∑ i ∈ Finset.range (n - k + 1),
          ascendingNaplesOneCount i (k - 1) * ascendingNaplesOneCount (n - k - i) k

/-- **Ascending $1$-Naples parking functions starting with $1$ and Fine numbers.** For every
natural number $n$, the number $U_{n,1}$ of weakly increasing $1$-Naples parking functions of
length $n$ whose first entry is $1$ equals the Fine number $F(n + 1)$, where the Fine numbers
$1, 0, 1, 2, 6, 18, \dots$ are indexed so that $F(0) = 1$ and $F(1) = 0$ (OEIS A000957).

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 4. -/
public theorem_wanted ascendingNaplesOneCount_one_eq_fineNumber (n : ℕ) :
    (ascendingNaplesOneCount n 1 : ℚ) = fineNumber (n + 1)

/-- **Counting ascending $1$-Naples parking functions.** For every natural number $n$, let
$I_{n,1}$ be the number of weakly increasing $1$-Naples parking functions of length $n$. Then
$$I_{n,1} = \sum_{i=0}^{n} C_i \, F(n - i),$$
where $C_i$ is the $i$-th Catalan number and $F$ is the sequence of Fine numbers, indexed so that
$F(0) = 1$ and $F(1) = 0$. This is the convolution of the Catalan and Fine numbers (OEIS A000958).

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 5. -/
public theorem_wanted ascendingNaplesCount_one_eq_sum (n : ℕ) :
    (ascendingNaplesCount n 1 : ℚ) =
      ∑ i ∈ Finset.range (n + 1), (catalan i : ℚ) * fineNumber (n - i)

/-- **Generating functions for ascending $k$-Naples parking functions.** Let $I_{n,k}$ be the
number of weakly increasing $k$-Naples parking functions of length $n$, let $U_{n,k}$ be the
number of those whose first entry is $1$, and let $C_k$ be the $k$-th Catalan number. Write
$I_k(x) = \sum_{n \ge 0} I_{n,k} x^n$ and $U_k(x) = \sum_{n \ge 0} U_{n,k} x^n$, formal power
series with natural number coefficients. For every natural number $k \ge 1$,
$$I_k(x) = I_{k-1}(x) + C_k x^k I_{k-1}(x) U_k(x)$$
and
$$U_k(x) = U_{k-1}(x) + C_k x^k U_{k-1}(x) U_k(x).$$

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 6. -/
public theorem_wanted ascendingNaples_generatingFunction {k : ℕ} (hk : 1 ≤ k) :
    PowerSeries.mk (fun n => ascendingNaplesCount n k) =
        PowerSeries.mk (fun n => ascendingNaplesCount n (k - 1)) +
          (catalan k : PowerSeries ℕ) * PowerSeries.X ^ k *
            PowerSeries.mk (fun n => ascendingNaplesCount n (k - 1)) *
            PowerSeries.mk (fun n => ascendingNaplesOneCount n k) ∧
      PowerSeries.mk (fun n => ascendingNaplesOneCount n k) =
        PowerSeries.mk (fun n => ascendingNaplesOneCount n (k - 1)) +
          (catalan k : PowerSeries ℕ) * PowerSeries.X ^ k *
            PowerSeries.mk (fun n => ascendingNaplesOneCount n (k - 1)) *
            PowerSeries.mk (fun n => ascendingNaplesOneCount n k)

/-- **Lattice path of a parking preference.** Let $\alpha = (a_1, \dots, a_n)$ be a sequence of
natural numbers. Its lattice path is the sequence of $2n$ steps, each an Up step $(1, 1)$ or a
Down step $(1, -1)$, obtained by taking, for each spot $s = 1, \dots, n$ in turn, one Up step
for every index $i$ with $a_i = s$ followed by one Down step, and then appending Down steps
until there are $2n$ steps. When every $a_i$ lies in $\{1, \dots, n\}$ this gives exactly $2n$
steps and nothing is appended; if moreover $\alpha$ is weakly increasing, the $i$-th Up step is
preceded by exactly $a_i - 1$ Down steps.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 3 (Remark 3.3). -/
public def preferencePath {n : ℕ} (α : Fin n → ℕ) : Fin (2 * n) → Bool := fun j =>
  ((List.range n).flatMap fun s =>
    List.replicate (Finset.univ.filter fun i => α i = s + 1).card true ++ [false]).getD j false

/-- **The lattice path of $(1, 3, 3, 5, 6, 6)$.** The lattice path of the parking preference
$(1, 3, 3, 5, 6, 6)$ is $\mathrm{UDDUUDDUDUUD}$, where $\mathrm{U}$ is an Up step and
$\mathrm{D}$ a Down step.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 3 (Figure 3). -/
public theorem preferencePath_example :
    preferencePath ![1, 3, 3, 5, 6, 6] =
      ![true, false, false, true, true, false, false, true, false, true, true, false] := by
  decide

/-- **Lattice-path criterion for ascending $k$-Naples parking functions.** Let
$\alpha = (a_1, \dots, a_n)$ be a weakly increasing preference with $1 \le a_i \le n$ for every
$i$, and let $h_j$ be the height after the first $j$ steps of the lattice path of $\alpha$, which
has $2n$ steps. Then $\alpha$ is a $k$-Naples parking function if and only if for every $j$
with $1 \le j \le 2n$ and $h_j < 0$ there is a $j'$ with $j < j' \le j + 2k$, $j' \le 2n$ and
$h_{j'} > 0$.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 2.6 (published as Theorem 2). -/
public theorem_wanted isNaplesParkingFunction_iff_of_monotone {n k : ℕ} {α : Fin n → ℕ}
    (hα : ∀ i, 1 ≤ α i ∧ α i ≤ n) (hmono : Monotone α) :
    IsNaplesParkingFunction k α ↔
      ∀ i < 2 * n, latticeHeight (preferencePath α) (i + 1) < 0 →
        ∃ j, i + 1 < j ∧ j ≤ i + 1 + 2 * k ∧ j ≤ 2 * n ∧
          0 < latticeHeight (preferencePath α) j

/-- **When every rearrangement of a preference is $k$-Naples.** Let
$\alpha = (a_1, \dots, a_n) \in \{1, \dots, n\}^n$ and let $P$ be its lattice path: for each
spot $s = 1, \dots, n$ in turn, one Up step for every car preferring $s$, then one Down step
(this is also the lattice path of the ascending rearrangement of $\alpha$). The height of $P$
after $m$ steps is the number of Up steps minus the number of Down steps among its first $m$
steps. Then every rearrangement of $\alpha$ is a $k$-Naples parking function if and only if,
for every $i$ with $1 \le i \le 2n$ such that the height of $P$ after $i$ steps is negative,
there is a $j$ with $i < j \le i + 2k$ and $j \le 2n$ such that the height of $P$ after $j$
steps is positive.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Corollary 2.7 (published as Corollary 1). -/
public theorem_wanted forall_perm_isNaplesParkingFunction_iff {n k : ℕ} {α : Fin n → ℕ}
    (hα : ∀ i, 1 ≤ α i ∧ α i ≤ n) :
    (∀ σ : Equiv.Perm (Fin n), IsNaplesParkingFunction k (α ∘ σ)) ↔
      ∀ i < 2 * n, latticeHeight (preferencePath α) (i + 1) < 0 →
        ∃ j, i + 1 < j ∧ j ≤ i + 1 + 2 * k ∧ j ≤ 2 * n ∧
          0 < latticeHeight (preferencePath α) j

open Classical in
/-- **Ascending $k$-Naples parking functions and Dyck paths.** For all natural numbers $n \ge 1$
and $k$, the number of weakly increasing $k$-Naples parking functions of length $n$ equals the
number of Dyck paths of semilength $n + k$ (that is, with $2(n + k)$ steps) whose first $k$ steps
are Up, whose last $k + 1$ steps are Down, and which satisfy the following condition. Writing
$h_j$ for the height after the first $j$ steps, whenever the $m$-th step is a Down step that is
not among the last $k + 1$ steps and $h_m < k$, there is a $j$ with $m < j \le m + 2k$ and
$j \le 2(n + k)$ such that $h_j > k$.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Corollary 2.12 (published as Corollary 3). -/
public theorem_wanted ascendingNaplesCount_eq_card_dyckPath {n k : ℕ} (hn : 1 ≤ n) :
    ascendingNaplesCount n k = (Finset.univ.filter fun p : {p : DyckWord // p.semilength = n + k} =>
      List.replicate k DyckStep.U <+: p.1.toList ∧
        List.replicate (k + 1) DyckStep.D <:+ p.1.toList ∧
        ∀ i, i + (k + 1) < 2 * (n + k) → p.1.toList[i]? = some DyckStep.D →
          dyckStepHeight p.1.toList (i + 1) < k →
            ∃ j, i + 1 < j ∧ j ≤ i + 1 + 2 * k ∧ j ≤ 2 * (n + k) ∧
              (k : ℤ) < dyckStepHeight p.1.toList j).card

/-- **Left spine lengths of small binary trees.** The empty binary tree has left spine length
$0$, and the binary tree with three nodes, a root whose left child and right child have no
children, has left spine length $2$.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 4 (Proposition 4.12). -/
public theorem leftSpineLength_examples :
    leftSpineLength (BinaryTree.nil : BinaryTree Unit) = 0 ∧
      leftSpineLength (BinaryTree.node () (BinaryTree.node () .nil .nil)
        (BinaryTree.node () .nil .nil)) = 2 := by
  decide

/-- **Edges of an inscribed polygon.** Let $R$ be a set of vertices of the convex $s$-gon with
vertices $0, 1, \dots, s - 1$. The edges of the polygon with vertex set $R$ are the pairs
$(a, b)$ of elements of $R$ with $a < b$ such that either no element of $R$ lies strictly
between $a$ and $b$, or $a$ is the least and $b$ the greatest element of $R$.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 6 (Theorem 6.3). -/
public def inscribedPolygonEdges {s : ℕ} (R : Finset (Fin s)) : Finset (Fin s × Fin s) :=
  (R ×ˢ R).filter fun e => e.1 < e.2 ∧
    ((∀ c ∈ R, ¬ (e.1 < c ∧ c < e.2)) ∨ ∀ c ∈ R, e.1 ≤ c ∧ c ≤ e.2)

/-- **$r$-in-$s$ dissection.** Let $D$ be a set of pairs $(a, b)$ of vertices of the convex
$s$-gon with vertices $0, 1, \dots, s - 1$, and let $R$ be a set of its vertices. Then $D$ is
an $r$-in-$s$ dissection with inner polygon $R$ when all of the following hold: the number of
elements of $D$ plus $r$ equals $s$, and $R$ has $r$ elements; every $(a, b) \in D$ is a
diagonal, that is, $a + 2 \le b$ and $(a, b) \ne (0, s - 1)$; no $(a, b)$ and $(c, d)$ in $D$
cross, that is, $a < c < b < d$ never holds; every edge of the polygon with vertex set $R$ is a
side of the $s$-gon, $(a, a + 1)$ or $(0, s - 1)$, or lies in $D$; and every element of $D$
with both endpoints in $R$ is an edge of the polygon with vertex set $R$.

The remaining $s - r$ faces of such a dissection are triangles.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 6 (Definition 6.1). -/
public def IsInnerPolygonDissection (s r : ℕ) (D : Finset (Fin s × Fin s))
    (R : Finset (Fin s)) : Prop :=
  D.card + r = s ∧ R.card = r ∧
    (∀ e ∈ D, e.1.val + 2 ≤ e.2.val ∧ ¬ (e.1.val = 0 ∧ e.2.val + 1 = s)) ∧
    (∀ e ∈ D, ∀ f ∈ D, ¬ (e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2)) ∧
    (∀ e ∈ inscribedPolygonEdges R,
      e.2.val = e.1.val + 1 ∨ (e.1.val = 0 ∧ e.2.val + 1 = s) ∨ e ∈ D) ∧
    ∀ e ∈ D, e.1 ∈ R → e.2 ∈ R → e ∈ inscribedPolygonEdges R

public instance (s r : ℕ) (D : Finset (Fin s × Fin s)) (R : Finset (Fin s)) :
    Decidable (IsInnerPolygonDissection s r D R) := by
  unfold IsInnerPolygonDissection
  exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
    (@instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ inferInstance inferInstance))))

/-- **Examples of $r$-in-$s$ dissections.** For the convex polygons with vertices
$0, 1, \dots, s - 1$: the square ($s = 4$) with no diagonals is a $4$-in-$4$ dissection whose
quadrilateral has all four vertices; the pentagon ($s = 5$) with the single diagonal $(0, 2)$
is a $4$-in-$5$ dissection with quadrilateral on the vertices $0, 2, 3, 4$, but not with
quadrilateral on the vertices $0, 1, 2, 3$.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 6 (Definition 6.1). -/
public theorem isInnerPolygonDissection_examples :
    IsInnerPolygonDissection 4 4 ∅ Finset.univ ∧
      IsInnerPolygonDissection 5 4 {(0, 2)} {0, 2, 3, 4} ∧
      ¬ IsInnerPolygonDissection 5 4 {(0, 2)} {0, 1, 2, 3} := by
  decide

open Classical in
/-- **Descending strictly $k$-Naples parking functions and polygon dissections.** Let $n$ and
$k \ge 1$ be natural numbers and let $s = n + k + 1$. Then $s$ times the number of weakly
decreasing preferences of length $n$ that are $k$-Naples but not $(k - 1)$-Naples parking
functions equals the number of triples $(D, R, e)$ such that the set of diagonals $D$ and the
vertex set $R$ form a $(2k + 2)$-in-$s$ dissection of the convex $s$-gon with vertices
$0, \dots, s - 1$, and $e$ is an edge of the inscribed polygon with vertex set $R$.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 6.3 (published as Proposition 6). -/
public theorem_wanted mul_descendingStrictNaplesCount_eq_card_dissection {n k : ℕ}
    (hk : 1 ≤ k) :
    (n + k + 1) * descendingStrictNaplesCount n k =
      (Finset.univ.filter fun x : Finset (Fin (n + k + 1) × Fin (n + k + 1)) ×
          Finset (Fin (n + k + 1)) × (Fin (n + k + 1) × Fin (n + k + 1)) =>
        IsInnerPolygonDissection (n + k + 1) (2 * k + 2) x.1 x.2.1 ∧
          x.2.2 ∈ inscribedPolygonEdges x.2.1).card

open Classical in
/-- **Descending strictly $k$-Naples parking functions and noncrossing partitions.** For every
$n$ and every $k \ge 1$, the number of descending strictly $k$-Naples parking functions of
length $n$ (descending preferences that are $k$-Naples but not $(k - 1)$-Naples) equals the
number of noncrossing partitions of $\{0, 1, \dots, n + k\}$ in which the block containing $0$
has exactly $2k + 2$ elements.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 6.4 (published as Proposition 7). -/
public theorem_wanted descendingStrictNaplesCount_eq_card_noncrossingPartition {n k : ℕ}
    (hk : 1 ≤ k) :
    descendingStrictNaplesCount n k = (Finset.univ.filter
      fun P : NoncrossingPartition (n + k + 1) =>
        (NoncrossingPartition.block P 0).card = 2 * k + 2).card

end

end MetaMathlibExt
