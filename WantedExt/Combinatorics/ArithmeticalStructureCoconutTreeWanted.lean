/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat

namespace MetaMathlibExt

@[expose] public section

/-! Statements from Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith,
*Arithmetical Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82
(preprint arXiv:2406.11183, whose text supplies the definitions).

The coconut tree `CT(p, s)` has vertex type `Fin p ⊕ Fin s`: the path vertex
`v_{i+1}` is `.inl i` and the leaf `v_{ℓ_{j+1}}` is `.inr j`; the central vertex
`v_p` is `.inl ⟨p - 1, _⟩`. A structure `(d, r)` is a pair of labelings of the
vertices. Counts `|Arith(G)|` and `|SArith(G)|` are `Set.ncard` of the sets of
pairs `(d, r)`. -/

/-- **Arithmetical structure.** An arithmetical structure on a graph $G$ with vertex set $V$ is a
pair of labelings $d, r : V \to \mathbb{N}$ such that $d(v) > 0$ and $r(v) > 0$ for every vertex
$v$, $d(v)\, r(v) = \sum_{w \sim v} r(w)$ for every vertex $v$, where the sum runs over the
neighbours $w$ of $v$, and the only natural number dividing every $r(v)$ is $1$. For a finite graph
with adjacency matrix $A$ the middle condition reads $(\operatorname{diag}(d) - A)\, r = 0$.

The neighbour sum is taken to be $0$ when $v$ has infinitely many neighbours, so no arithmetical
structure exists on a graph with a vertex of infinite degree.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.1
(arXiv numbering). -/
public def IsArithmeticalStructure {V : Type*} (G : SimpleGraph V) (d r : V → ℕ) : Prop :=
  (∀ v, 0 < d v) ∧ (∀ v, 0 < r v) ∧
    (∀ v, d v * r v = ∑ᶠ w ∈ {w | G.Adj v w}, r w) ∧
    ∀ g : ℕ, (∀ v, g ∣ r v) → g = 1

/-- **The all-ones structure on a single edge.** On the graph with two vertices joined by an edge,
the labelings $d = (1, 1)$ and $r = (1, 1)$ form an arithmetical structure.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.1
(arXiv numbering). -/
public theorem isArithmeticalStructure_top_fin_two :
    IsArithmeticalStructure (⊤ : SimpleGraph (Fin 2)) 1 1 := by
  refine ⟨fun _ => one_pos, fun _ => one_pos, fun v => ?_, fun g hg => Nat.dvd_one.mp (hg 0)⟩
  rcases (show v = 0 ∨ v = 1 by fin_cases v <;> simp) with rfl | rfl
  · have : {w : Fin 2 | (⊤ : SimpleGraph (Fin 2)).Adj 0 w} = {1} := by
      ext w; fin_cases w <;> simp
    rw [this, finsum_mem_singleton]
    rfl
  · have : {w : Fin 2 | (⊤ : SimpleGraph (Fin 2)).Adj 1 w} = {0} := by
      ext w; fin_cases w <;> simp
    rw [this, finsum_mem_singleton]
    rfl

/-- **Coconut tree.** For natural numbers $p$ and $s$, the coconut tree $\mathrm{CT}(p, s)$ is the
graph whose vertices are the path vertices $v_1, \dots, v_p$ and the leaves
$v_{\ell_1}, \dots, v_{\ell_s}$, in which $v_i$ and $v_{i+1}$ are adjacent for $1 \le i < p$, every
leaf is adjacent to $v_p$, and there are no other edges. For $p = 0$ it consists of $s$ isolated
vertices.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.2
(arXiv numbering). -/
public def coconutTree (p s : ℕ) : SimpleGraph (Fin p ⊕ Fin s) :=
  SimpleGraph.fromRel fun a b =>
    match a, b with
    | .inl i, .inl j => i.val + 1 = j.val
    | .inl i, .inr _ => i.val + 1 = p
    | .inr _, _ => False

/-- **Adjacent path vertices of a coconut tree.** Let the coconut tree $CT(p, s)$ have path
vertices $v_1, \dots, v_p$. Two path vertices $v_a$ and $v_b$ are adjacent if and only if
$|a - b| = 1$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.2
(arXiv numbering). -/
public theorem coconutTree_adj_inl_inl {p s : ℕ} (i j : Fin p) :
    (coconutTree p s).Adj (.inl i) (.inl j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simp only [coconutTree, SimpleGraph.fromRel_adj, ne_eq, Sum.inl.injEq]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨fun hij => ?_, h⟩
    subst hij
    omega

/-- **Adjacency of leaves and path vertices in a coconut tree.** Let the coconut tree
$CT(p, s)$ have path vertices $v_1, \dots, v_p$, with central vertex $v_p$. A leaf of $CT(p, s)$
is adjacent to a path vertex $v_k$ if and only if $k = p$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.2
(arXiv numbering). -/
public theorem coconutTree_adj_inl_inr {p s : ℕ} (i : Fin p) (j : Fin s) :
    (coconutTree p s).Adj (.inl i) (.inr j) ↔ i.val + 1 = p := by
  simp [coconutTree, SimpleGraph.fromRel_adj]

/-- **Leaves of a coconut tree are pairwise nonadjacent.** No leaf of the coconut tree $CT(p, s)$
is adjacent to a leaf.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.2
(arXiv numbering). -/
public theorem coconutTree_not_adj_inr_inr {p s : ℕ} (j j' : Fin s) :
    ¬(coconutTree p s).Adj (.inr j) (.inr j') := by
  simp [coconutTree, SimpleGraph.fromRel_adj]

/-- **Smooth arithmetical structure on a coconut tree.** Let $CT(p, s)$ be the coconut tree with
path vertices $v_1, \dots, v_p$ and leaves $\ell_1, \dots, \ell_s$ adjacent to $v_p$. An
arithmetical structure $(d, r)$ on $CT(p, s)$ is smooth if $d(v_i) \ge 2$ for $1 \le i \le p - 1$
and $d(\ell_j) \ge 2$ for $1 \le j \le s$; there is no condition on $d(v_p)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.3
(arXiv numbering). -/
public def IsSmoothCoconut (p s : ℕ) (d r : Fin p ⊕ Fin s → ℕ) : Prop :=
  IsArithmeticalStructure (coconutTree p s) d r ∧
    (∀ i : Fin p, i.val + 1 < p → 2 ≤ d (.inl i)) ∧ ∀ j, 2 ≤ d (.inr j)

/-- **Leaves of a smooth coconut structure have label at least 2.** If $(d, r)$ is a smooth
arithmetical structure on the coconut tree $\mathrm{CT}(p, s)$, then $d_{\ell_j} \ge 2$ for every
leaf $\ell_j$, $1 \le j \le s$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.3
(arXiv numbering). -/
public theorem IsSmoothCoconut.two_le_leaf {p s : ℕ} {d r : Fin p ⊕ Fin s → ℕ}
    (h : IsSmoothCoconut p s d r) (j : Fin s) : 2 ≤ d (.inr j) :=
  h.2.2 j

/-- **Ballot numbers.** For natural numbers $n$ and $k$, the ballot number $B(n, k)$ is the
integer part of $\max(n + 1 - k, 0) \binom{n+k}{n} / (n + 1)$. For $k \le n + 1$ the division
is exact, so $B(n, k) = \frac{n - k + 1}{n + 1} \binom{n+k}{n}$ (OEIS A009766), and
$B(n, k) = 0$ for $k > n + 1$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Section 1. -/
public def ballotNumber (n k : ℕ) : ℕ :=
  (n + 1 - k) * (n + k).choose n / (n + 1)

/-- **Ballot numbers with second index zero.** For every natural number $n$, the ballot number
$B(n, 0)$ equals $1$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Section 1. -/
public theorem ballotNumber_zero_right (n : ℕ) : ballotNumber n 0 = 1 := by
  simp [ballotNumber]

/-- **Diagonal ballot numbers are Catalan numbers.** For every natural number $n$, the ballot
number $B(n, n)$ equals the $n$-th Catalan number $C_n$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Section 1. -/
public theorem ballotNumber_self (n : ℕ) : ballotNumber n n = catalan n := by
  rw [ballotNumber, show n + 1 - n = 1 by omega, one_mul, ← two_mul,
    ← Nat.centralBinom_eq_two_mul_choose, ← succ_mul_catalan_eq_centralBinom,
    Nat.mul_div_cancel_left _ (Nat.succ_pos n)]

/-- **Terms of the coconut tree count.** For natural numbers $x$ and $y$, the term $A(x, y)$ is
defined by $A(x, 0) = C_{x-1}$, $A(x, 1) = C_{x-1} - C_{x-2}$ and, for $y \ge 2$,

$$A(x, y) = \sum_{i=y+1}^{x} B(x - y - 1, x - i) \, |\mathrm{SArith}(CT(i - y, y))|,$$

where $C_n$ is the $n$-th Catalan number (a negative index is read as $0$), $B$ is the ballot
number, and $|\mathrm{SArith}(CT(m, y))|$ is the number of smooth arithmetical structures
$(d, r)$ on the coconut tree $CT(m, y)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Theorem 1. -/
public noncomputable def coconutCountTerm (x y : ℕ) : ℕ :=
  if y = 0 then catalan (x - 1)
  else if y = 1 then catalan (x - 1) - catalan (x - 2)
  else ∑ i ∈ Finset.Icc (y + 1) x, ballotNumber (x - y - 1) (x - i) *
    Set.ncard {z : (Fin (i - y) ⊕ Fin y → ℕ) × (Fin (i - y) ⊕ Fin y → ℕ) |
      IsSmoothCoconut (i - y) y z.1 z.2}

/-- **The coconut count term with second argument zero.** For every natural number $x$, the
term $A(x, 0)$ of the coconut tree count equals the Catalan number $C_{x-1}$, read as $C_0$
when $x = 0$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Theorem 1. -/
public theorem coconutCountTerm_zero (x : ℕ) : coconutCountTerm x 0 = catalan (x - 1) := by
  simp [coconutCountTerm]

/-- **Euclidean chain function.** For natural numbers $x_1$ and $x_2$, the Euclidean chain
$x_1, x_2, x_3, \dots$ is given by $x_{i+1} = (-x_{i-1}) \bmod x_i$ (the least nonnegative
residue) while $x_i \ne 0$, and by $x_{i+1} = 0$ once $x_i = 0$. The Euclidean chain function is
defined by the recursion $F(x, 0) = 1$ and $F(x, y) = 1 + F(y, (-x) \bmod y)$ for $y \ne 0$. For
$x_1 > 0$, $F(x_1, x_2)$ is the number of positive terms of the Euclidean chain.

For $x_1 = 0$ the recursion also counts the first term $0$: $F(0, 0) = 1$ and $F(0, 1) = 2$,
although the chains $0, 0$ and $0, 1, 0$ have $0$ and $1$ positive terms.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 4.12
(arXiv numbering). -/
public def euclideanChainLength (x y : ℕ) : ℕ :=
  if h : y = 0 then 1 else 1 + euclideanChainLength y ((y - x % y) % y)
termination_by y
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

/-- **Euclidean chain function with second argument zero.** For every natural number $x$, the
Euclidean chain function $F$ satisfies $F(x, 0) = 1$.

For $x = 0$ this is the value given by the recursive definition of $F$, not a count of positive
terms.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 4.12
(arXiv numbering). -/
public theorem euclideanChainLength_zero (x : ℕ) : euclideanChainLength x 0 = 1 := by
  rw [euclideanChainLength]
  simp

/-- **Recursion for the Euclidean chain function.** For natural numbers $x$ and $y$ with $y \ne 0$,
the Euclidean chain function $F$ satisfies $F(x, y) = 1 + F(y, (-x) \bmod y)$, where
$(-x) \bmod y$ is the least nonnegative residue of $-x$ modulo $y$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 4.12
(arXiv numbering). -/
public theorem euclideanChainLength_of_ne_zero (x : ℕ) {y : ℕ} (hy : y ≠ 0) :
    euclideanChainLength x y = 1 + euclideanChainLength y ((y - x % y) % y) := by
  rw [euclideanChainLength]
  simp [hy]

/-- **Euclidean chain function of 13 and 60.** The Euclidean chain function $F$ satisfies
$F(13, 60) = 8$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Example 4.13
(arXiv numbering). -/
public theorem euclideanChainLength_thirteen_sixty : euclideanChainLength 13 60 = 8 := by
  simp [euclideanChainLength_of_ne_zero, euclideanChainLength_zero]

/-- **Monotonicity criteria for arithmetical structures on coconut trees.** Let $(d, r)$ be an
arithmetical structure on the coconut tree $CT(p, s)$ with path vertices $v_1, \dots, v_p$, and
write $d_k = d(v_k)$ and $r_k = r(v_k)$. The following are equivalent: (1) $d_k \ge 2$ for
$1 \le k \le p - 1$; (2) $0 < r_2 - r_1 \le r_3 - r_2 \le \cdots \le r_p - r_{p-1}$; (3)
$r_1 < r_2 < \cdots < r_p$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Lemma 1
(`integers-2025-A82-lem-1`). -/
public theorem_wanted IsArithmeticalStructure.coconut_tfae {p s : ℕ}
    {d r : Fin p ⊕ Fin s → ℕ} (h : IsArithmeticalStructure (coconutTree p s) d r) :
    [∀ i : Fin p, i.val + 1 < p → 2 ≤ d (.inl i),
      (∀ hp : 1 < p, r (.inl ⟨0, by omega⟩) < r (.inl ⟨1, hp⟩)) ∧
        ∀ (i : ℕ) (hi : i + 2 < p),
          (r (.inl ⟨i + 1, by omega⟩) : ℤ) - r (.inl ⟨i, by omega⟩)
            ≤ (r (.inl ⟨i + 2, hi⟩) : ℤ) - r (.inl ⟨i + 1, by omega⟩),
      StrictMono fun i : Fin p => r (.inl i)].TFAE

/-- **Characterization of smooth coconut structures.** Let $p \ge 1$ and let $(d, r)$ be an
arithmetical structure on the coconut tree $CT(p, s)$ with path vertices $v_1, \dots, v_p$ and
leaves $\ell_1, \dots, \ell_s$ adjacent to $v_p$. Then $(d, r)$ is smooth if and only if
$r(\ell_j) < r(v_p)$ for every $j$ and $r(v_1) < r(v_2) < \dots < r(v_p)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Lemma 2
(`integers-2025-A82-lem-2`). -/
public theorem_wanted IsArithmeticalStructure.isSmoothCoconut_iff {p s : ℕ}
    {d r : Fin p ⊕ Fin s → ℕ} (hp : 0 < p)
    (h : IsArithmeticalStructure (coconutTree p s) d r) :
    IsSmoothCoconut p s d r ↔
      (∀ j, r (.inr j) < r (.inl ⟨p - 1, by omega⟩)) ∧ StrictMono fun i : Fin p => r (.inl i)

/-- **The leaf labels of a smooth arithmetical structure on a coconut tree are coprime.** Let
$(d, r)$ be a smooth arithmetical structure on the coconut tree $\mathrm{CT}(p, s)$ with leaves
$v_{\ell_1}, \dots, v_{\ell_s}$. If a natural number $g$ divides $r(v_{\ell_j})$ for every
$j = 1, \dots, s$, then $g = 1$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Lemma 3
(`integers-2025-A82-lem-3`). -/
public theorem_wanted IsSmoothCoconut.eq_one_of_dvd_leaves {p s : ℕ}
    {d r : Fin p ⊕ Fin s → ℕ} (h : IsSmoothCoconut p s d r) {g : ℕ}
    (hg : ∀ j, g ∣ r (.inr j)) : g = 1

/-- **Arithmetical structures on a one-leaf coconut tree with a non-smoothable leaf.** For every
integer $p \ge 1$, the number of arithmetical structures $(d, r)$ on the coconut tree
$\mathrm{CT}(p, 1)$, which is the path on $p + 1$ vertices, whose leaf $\ell_1$ has
$d_{\ell_1} \ne 1$ (so that the leaf cannot be smoothed) is $C_p - C_{p-1}$, where $C_n$
denotes the $n$-th Catalan number.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 5
(`integers-2025-A82-prop-5`). -/
public theorem_wanted ncard_arithmeticalStructure_coconutTree_one_leaf_ne_one {p : ℕ}
    (hp : 1 ≤ p) :
    Set.ncard {x : (Fin p ⊕ Fin 1 → ℕ) × (Fin p ⊕ Fin 1 → ℕ) |
      IsArithmeticalStructure (coconutTree p 1) x.1 x.2 ∧ x.1 (.inr 0) ≠ 1}
      = catalan p - catalan (p - 1)

/-- **Number of arithmetical structures on coconut trees.** For $p \ge 1$ and $s \ge 2$, the number
of arithmetical structures on the coconut tree $CT(p, s)$ is
$$\sum_{j=0}^{s} \binom{s}{j} A(p + s - j, s - j),$$
where $A(x, y)$ is the coconut count term.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Theorem 1
(`integers-2025-A82-thm-1`). -/
public theorem_wanted ncard_arithmeticalStructure_coconutTree {p s : ℕ} (hp : 1 ≤ p)
    (hs : 2 ≤ s) :
    Set.ncard {x : (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ) |
      IsArithmeticalStructure (coconutTree p s) x.1 x.2}
      = ∑ j ∈ Finset.range (s + 1), s.choose j * coconutCountTerm (p + s - j) (s - j)

/-- **Number of arithmetical structures on coconut trees with two leaves.** For $p \ge 2$, the
number of arithmetical structures on the coconut tree $CT(p, 2)$ is
$$2 C_p - C_{p-1} + \sum_{i=3}^{p+2} B(p - 1, p + 2 - i)\, N(i - 2),$$
where $C_n$ is the $n$-th Catalan number, $B(n, k)$ is the ballot number and $N(q)$ is the number
of smooth arithmetical structures on $CT(q, 2)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 2
(`integers-2025-A82-cor-2`). -/
public theorem_wanted ncard_arithmeticalStructure_coconutTree_two {p : ℕ} (hp : 2 ≤ p) :
    Set.ncard {x : (Fin p ⊕ Fin 2 → ℕ) × (Fin p ⊕ Fin 2 → ℕ) |
      IsArithmeticalStructure (coconutTree p 2) x.1 x.2}
      = 2 * catalan p - catalan (p - 1) + ∑ i ∈ Finset.Icc 3 (p + 2),
          ballotNumber (p - 1) (p + 2 - i) *
            Set.ncard {z : (Fin (i - 2) ⊕ Fin 2 → ℕ) × (Fin (i - 2) ⊕ Fin 2 → ℕ) |
              IsSmoothCoconut (i - 2) 2 z.1 z.2}

/-- **Number of arithmetical structures on stars.** For $s \ge 2$, the number of arithmetical
structures on the star $CT(1, s)$, a centre joined to $s$ leaves, is
$$1 + \sum_{j=0}^{s-2} \binom{s}{j} N(s - j),$$
where $N(t)$ is the number of smooth arithmetical structures on the star $CT(1, t)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 3
(`integers-2025-A82-cor-3`). -/
public theorem_wanted ncard_arithmeticalStructure_coconutTree_star {s : ℕ} (hs : 2 ≤ s) :
    Set.ncard {x : (Fin 1 ⊕ Fin s → ℕ) × (Fin 1 ⊕ Fin s → ℕ) |
      IsArithmeticalStructure (coconutTree 1 s) x.1 x.2}
      = 1 + ∑ j ∈ Finset.range (s - 1), s.choose j *
          Set.ncard {z : (Fin 1 ⊕ Fin (s - j) → ℕ) × (Fin 1 ⊕ Fin (s - j) → ℕ) |
            IsSmoothCoconut 1 (s - j) z.1 z.2}

/-- **Euclidean chain function under adding multiples.** For natural numbers $x \ge 1$, $y$ and
$k$, the Euclidean chain function $F$ satisfies $F(x + k y, y) = F(x, y)$ and
$F(x, k x + y) = F(x, y) + k$.

The source quotes this result from Archer et al.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 6
(`integers-2025-A82-prop-6`). -/
public theorem_wanted euclideanChainLength_add_mul {x : ℕ} (hx : 0 < x) (y k : ℕ) :
    euclideanChainLength (x + k * y) y = euclideanChainLength x y ∧
      euclideanChainLength x (k * x + y) = euclideanChainLength x y + k

/-- **Euclidean chain function when the first argument divides the second.** For natural numbers
$x, y \ge 1$ with $x \mid y$, the Euclidean chain function $F$ satisfies $F(x, y) = 1 + y / x$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 4
(`integers-2025-A82-cor-4`). -/
public theorem_wanted euclideanChainLength_of_dvd {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ∣ y) : euclideanChainLength x y = 1 + y / x

/-- **Euclidean chain function at one.** For every natural number $y$, the Euclidean chain
function $F$ satisfies $F(1, y) = y + 1$, and for every natural number $x \ge 1$ it satisfies
$F(x, 1) = 2$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 5
(`integers-2025-A82-cor-5`). -/
public theorem_wanted euclideanChainLength_one_left_and_one_right (y : ℕ) {x : ℕ}
    (hx : 0 < x) :
    euclideanChainLength 1 y = y + 1 ∧ euclideanChainLength x 1 = 2

/-- **Smooth coconut structures with prescribed labels.** Let $s \ge 1$ and let $c$ and
$a_1, \dots, a_s$ be natural numbers with $a_i > 0$, $a_i \mid c$ and $a_i < c$ for every $i$, such
that the only natural number dividing $c$ and all of $a_1, \dots, a_s$ is $1$. Write $CT(p, s)$ for
the coconut tree with path vertices $v_1, \dots, v_p$ and leaves $\ell_1, \dots, \ell_s$ adjacent
to $v_p$. Then there is exactly one $p \ge 1$ such that $CT(p, s)$ carries a smooth arithmetical
structure $(d, r)$ with $r(\ell_i) = a_i$ for every $i$ and $r(v_p) = c$. Moreover, for every
$p \ge 1$, any two smooth arithmetical structures $(d, r)$ and $(d', r')$ on $CT(p, s)$ with
$r(\ell_i) = r'(\ell_i) = a_i$ for every $i$ and $r(v_p) = r'(v_p) = c$ are equal.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 7
(`integers-2025-A82-prop-7`). -/
public theorem_wanted existsUnique_isSmoothCoconut {s : ℕ} (hs : 1 ≤ s) {c : ℕ}
    (a : Fin s → ℕ) (ha : ∀ i, 0 < a i) (hdvd : ∀ i, a i ∣ c) (hlt : ∀ i, a i < c)
    (hgcd : ∀ g : ℕ, g ∣ c → (∀ i, g ∣ a i) → g = 1) :
    (∃! p : ℕ, ∃ hp : 0 < p, ∃ d r : Fin p ⊕ Fin s → ℕ, IsSmoothCoconut p s d r ∧
        (∀ i, r (.inr i) = a i) ∧ r (.inl ⟨p - 1, by omega⟩) = c) ∧
      ∀ (p : ℕ) (hp : 0 < p) (d r d' r' : Fin p ⊕ Fin s → ℕ),
        IsSmoothCoconut p s d r → (∀ i, r (.inr i) = a i) →
        r (.inl ⟨p - 1, by omega⟩) = c →
        IsSmoothCoconut p s d' r' → (∀ i, r' (.inr i) = a i) →
        r' (.inl ⟨p - 1, by omega⟩) = c → d = d' ∧ r = r'

/-- **Path length of a smooth arithmetical structure on a coconut tree.** Let $F$ be the
Euclidean chain function, let $p \ge 1$, and let $(d, r)$ be a smooth arithmetical structure on
the coconut tree $\mathrm{CT}(p, s)$, with path vertices $v_1, \dots, v_p$ and leaves
$v_{\ell_1}, \dots, v_{\ell_s}$. Then $p = F(r(v_{\ell_1}) + \dots + r(v_{\ell_s}), r(v_p)) - 1$.

The source states this for the smooth arithmetical structure that Proposition 7 constructs from
labels $a_1, \dots, a_s$ and $c$; every smooth arithmetical structure is the one constructed from
its own labels $a_j = r(v_{\ell_j})$ and $c = r(v_p)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 6
(`integers-2025-A82-cor-6`). -/
public theorem_wanted IsSmoothCoconut.eq_euclideanChainLength_sub_one {p s : ℕ}
    (hp : 0 < p) {d r : Fin p ⊕ Fin s → ℕ} (h : IsSmoothCoconut p s d r) :
    p = euclideanChainLength (∑ j, r (.inr j)) (r (.inl ⟨p - 1, by omega⟩)) - 1

/-- **Smooth coconut structures with central label above one.** Let $p \ge 1$ and let $(d, r)$ be
a smooth arithmetical structure on the coconut tree $\mathrm{CT}(p, s)$, with central vertex $v_p$
and leaves $\ell_1, \ldots, \ell_s$. Then $d_{v_p} > 1$ if and only if
$r_{v_p} < \sum_{j=1}^{s} r_{\ell_j}$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 8
(`integers-2025-A82-prop-8`). -/
public theorem_wanted IsSmoothCoconut.one_lt_center_iff {p s : ℕ} (hp : 0 < p)
    {d r : Fin p ⊕ Fin s → ℕ} (h : IsSmoothCoconut p s d r) :
    1 < d (.inl ⟨p - 1, by omega⟩) ↔ r (.inl ⟨p - 1, by omega⟩) < ∑ j, r (.inr j)

/-- **Smooth structures on coconut trees with two leaves.** Let $p \ge 1$ and let $(d, r)$ be a
smooth arithmetical structure on the coconut tree $CT(p, 2)$, whose path is
$v_1, \dots, v_p$ and whose two leaves are attached to the central vertex $v_p$. Then
$d(v_p) \le 1$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 7
(`integers-2025-A82-cor-7`). -/
public theorem_wanted IsSmoothCoconut.center_le_one_of_two {p : ℕ} (hp : 0 < p)
    {d r : Fin p ⊕ Fin 2 → ℕ} (h : IsSmoothCoconut p 2 d r) :
    d (.inl ⟨p - 1, by omega⟩) ≤ 1

/-- **Smoothing at a path vertex of a coconut tree.** Let the coconut tree $CT(p + 1, s)$ have
path vertices $v_1, \dots, v_{p+1}$, central vertex $v_{p+1}$ and leaves $\ell_1, \dots, \ell_s$,
let $d$ and $r$ be labelings of its vertices by natural numbers, and let $1 \le k \le p + 1$.
Smoothing $(d, r)$ at $v_k$ gives the labelings $(d', r')$ of $CT(p, s)$ obtained by deleting
$v_k$ and renumbering the remaining path vertices $v_1, \dots, v_{k-1}, v_{k+1}, \dots, v_{p+1}$
in order as $v_1, \dots, v_p$. Every remaining vertex keeps its value of $r$ and its value of $d$,
except that $d$ drops by $1$ (truncated at $0$) at the path neighbours $v_{k-1}$ and $v_{k+1}$
of $v_k$, where they exist.

The paper applies it only at a non-central vertex ($k \le p$) with $d(v_k) = 1$: for $k \ge 2$
this is the degree-2 smoothing of Definition 3.1 and for $k = 1$ the smoothing at $v_1$ of
Definition 3.4.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definitions 3.1 and 3.4
(arXiv numbering). -/
public def coconutSmoothPath {p s : ℕ} (i : Fin (p + 1))
    (x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ)) :
    (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ) :=
  (Sum.elim
      (fun j => if j.val + 1 = i.val ∨ j.val = i.val then x.1 (.inl (i.succAbove j)) - 1
        else x.1 (.inl (i.succAbove j)))
      (fun l => x.1 (.inr l)),
    Sum.elim (fun j => x.2 (.inl (i.succAbove j))) (fun l => x.2 (.inr l)))

/-- **Smoothing at a leaf of a coconut tree.** Let the coconut tree $CT(p, s + 1)$ have path
vertices $v_1, \dots, v_p$, central vertex $v_p$ and leaves $\ell_1, \dots, \ell_{s+1}$, let $d$
and $r$ be labelings of its vertices by natural numbers, and let $1 \le k \le s + 1$. Smoothing
$(d, r)$ at the leaf $\ell_k$ gives the labelings $(d', r')$ of $CT(p, s)$ obtained by deleting
$\ell_k$ and renumbering the remaining leaves $\ell_1, \dots, \ell_{k-1}, \ell_{k+1}, \dots,
\ell_{s+1}$ in order as $\ell_1, \dots, \ell_s$. Every remaining vertex keeps its value of $r$
and its value of $d$, except that $d$ drops by $1$ (truncated at $0$) at the central vertex $v_p$
when $p \ge 1$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 3.4
(arXiv numbering). -/
public def coconutSmoothLeaf {p s : ℕ} (l : Fin (s + 1))
    (x : (Fin p ⊕ Fin (s + 1) → ℕ) × (Fin p ⊕ Fin (s + 1) → ℕ)) :
    (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ) :=
  (Sum.elim (fun j => if j.val + 1 = p then x.1 (.inl j) - 1 else x.1 (.inl j))
      (fun m => x.1 (.inr (l.succAbove m))),
    Sum.elim (fun j => x.2 (.inl j)) (fun m => x.2 (.inr (l.succAbove m))))

/-- **Subdivision at a path vertex of a coconut tree.** Let the coconut tree $CT(p, s)$ have path
vertices $v_1, \dots, v_p$ and leaves $\ell_1, \dots, \ell_s$, let $d$ and $r$ be labelings of
its vertices by natural numbers, and let $1 \le k \le p$. Subdividing $(d, r)$ at position $k$
gives the labelings $(d', r')$ of $CT(p + 1, s)$ obtained by inserting a new path vertex $w$
just before $v_k$, so that the path becomes $v_1, \dots, v_{k-1}, w, v_k, \dots, v_p$, with
$d'(w) = 1$ and $r'(w) = r(v_{k-1}) + r(v_k)$, where $r(v_0) = 0$ (so $r'(w) = r(v_1)$ when
$k = 1$). The path neighbours of $w$, namely $v_{k-1}$ (when $k \ge 2$) and $v_k$, get
$d' = d + 1$; every other vertex keeps its value of $d$, and every vertex other than $w$ keeps
its value of $r$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 3.9
(arXiv numbering). -/
public def coconutSubdivide {p s : ℕ} (i : Fin p)
    (x : (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ)) :
    (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ) :=
  let pd : ℕ → ℕ := fun t => if h : t < p then x.1 (.inl ⟨t, h⟩) else 0
  let pr : ℕ → ℕ := fun t => if h : t < p then x.2 (.inl ⟨t, h⟩) else 0
  (Sum.elim
      (fun j => if j.val + 1 < i.val then pd j.val
        else if j.val + 1 = i.val then pd j.val + 1
        else if j.val = i.val then 1
        else if j.val = i.val + 1 then pd (j.val - 1) + 1
        else pd (j.val - 1))
      (fun l => x.1 (.inr l)),
    Sum.elim
      (fun j => if j.val < i.val then pr j.val
        else if j.val = i.val then (if i.val = 0 then 0 else pr (i.val - 1)) + pr i.val
        else pr (j.val - 1))
      (fun l => x.2 (.inr l)))

/-- **Example of smoothing a coconut tree at a path vertex.** List a labeling of a coconut tree as
its values on the path vertices $v_1, v_2, \dots$, then $\mid$, then its values on the leaves.
Smoothing the labelings $d = (3, 1, 3, 2, 2 \mid 2, 2, 4)$ and $r = (1, 3, 2, 3, 4 \mid 2, 2, 1)$
of $CT(5, 3)$ at $v_2$ gives the labelings $d' = (2, 2, 2, 2 \mid 2, 2, 4)$ and
$r' = (1, 2, 3, 4 \mid 2, 2, 1)$ of $CT(4, 3)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Example 3.2
(arXiv numbering). -/
public theorem coconutSmoothPath_example :
    coconutSmoothPath (p := 4) (s := 3) 1
        (Sum.elim ![3, 1, 3, 2, 2] ![2, 2, 4], Sum.elim ![1, 3, 2, 3, 4] ![2, 2, 1]) =
      (Sum.elim ![2, 2, 2, 2] ![2, 2, 4], Sum.elim ![1, 2, 3, 4] ![2, 2, 1]) := by
  decide

/-- **An example of smoothing at a path vertex and at a leaf.** On the coconut tree $CT(4, 4)$,
write a labeling as (values at $v_1, \dots, v_4$ | values at the leaves $\ell_1, \dots, \ell_4$).
Take $d = (1, 3, 2, 3 \mid 2, 2, 3, 1)$ and $r = (2, 2, 4, 6 \mid 3, 3, 2, 6)$. Smoothing at the
path vertex $v_1$ and then at the leaf $\ell_4$ gives the labelings $d' = (2, 2, 2 \mid 2, 2, 3)$
and $r' = (2, 4, 6 \mid 3, 3, 2)$ on $CT(3, 3)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Example 3.5
(arXiv numbering). -/
public theorem coconutSmoothLeaf_example :
    coconutSmoothLeaf (p := 3) (s := 3) 3
        (coconutSmoothPath (p := 3) (s := 4) 0
          (Sum.elim ![1, 3, 2, 3] ![2, 2, 3, 1], Sum.elim ![2, 2, 4, 6] ![3, 3, 2, 6])) =
      (Sum.elim ![2, 2, 2] ![2, 2, 3], Sum.elim ![2, 4, 6] ![3, 3, 2]) := by
  decide

/-- **Example of subdividing a coconut tree.** List a labeling of a coconut tree as its values on
the path vertices $v_1, v_2, \dots$, then $\mid$, then its values on the leaves. Subdividing the
labelings $d = (2, 2, 2, 2 \mid 2, 2, 4)$ and $r = (1, 2, 3, 4 \mid 2, 2, 1)$ of $CT(4, 3)$ at
position $2$ gives the labelings $d' = (3, 1, 3, 2, 2 \mid 2, 2, 4)$ and
$r' = (1, 3, 2, 3, 4 \mid 2, 2, 1)$ of $CT(5, 3)$. These are the labelings of Example 3.2, whose
smoothing at $v_2$ is $(d, r)$, so here subdivision undoes that smoothing.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 3.9 and
Example 3.2 (arXiv numbering). -/
public theorem coconutSubdivide_example :
    coconutSubdivide (p := 4) (s := 3) 1
        (Sum.elim ![2, 2, 2, 2] ![2, 2, 4], Sum.elim ![1, 2, 3, 4] ![2, 2, 1]) =
      (Sum.elim ![3, 1, 3, 2, 2] ![2, 2, 4], Sum.elim ![1, 3, 2, 3, 4] ![2, 2, 1]) := by
  decide

/-- **Ancestors of labelings of coconut trees.** Let $x$ be a pair of vertex labelings $(d, r)$
of the coconut tree $CT(p, s)$ and $y$ a pair of vertex labelings of $CT(q, t)$. Then $y$ is an
ancestor of $x$, and $x$ a descendant of $y$, when $y$ is obtained from $x$ by a finite,
possibly empty, sequence of smoothings, each performed at a vertex where the current
$d$-label equals $1$: either at a path vertex other than the central vertex, or at a leaf.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 3.7
(ancestors and descendants; arXiv numbering). -/
public inductive CoconutAncestor : (p s : ℕ) → (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ) →
    (q t : ℕ) → (Fin q ⊕ Fin t → ℕ) × (Fin q ⊕ Fin t → ℕ) → Prop
  | refl {p s : ℕ} (x : (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ)) : CoconutAncestor p s x p s x
  | smoothPath {p s q t : ℕ} (x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ))
      (y : (Fin q ⊕ Fin t → ℕ) × (Fin q ⊕ Fin t → ℕ)) (i : Fin (p + 1)) (hi : i.val < p)
      (hd : x.1 (.inl i) = 1) (h : CoconutAncestor p s (coconutSmoothPath i x) q t y) :
      CoconutAncestor (p + 1) s x q t y
  | smoothLeaf {p s q t : ℕ} (x : (Fin p ⊕ Fin (s + 1) → ℕ) × (Fin p ⊕ Fin (s + 1) → ℕ))
      (y : (Fin q ⊕ Fin t → ℕ) × (Fin q ⊕ Fin t → ℕ)) (l : Fin (s + 1))
      (hd : x.1 (.inr l) = 1) (h : CoconutAncestor p s (coconutSmoothLeaf l x) q t y) :
      CoconutAncestor p (s + 1) x q t y

/-- **Path smoothing preserves arithmetical structures on coconut trees.** Let $s \ge 1$ and let
$(d, r)$ be an arithmetical structure on the coconut tree $CT(p + 1, s)$, whose path vertices are
$v_1, \dots, v_{p+1}$ with central vertex $v_{p+1}$. If $d(v_k) = 1$ for some non-central path
vertex $v_k$ (that is, $1 \le k \le p$), then smoothing $(d, r)$ at $v_k$ gives an arithmetical
structure on $CT(p, s)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 3.3
(`integers-2025-A82-prop-1`) and Proposition 3.6 for `i = 1` (`integers-2025-A82-prop-2`). -/
public theorem_wanted IsArithmeticalStructure.coconutSmoothPath {p s : ℕ} (hs : 1 ≤ s)
    {x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ)}
    (hx : IsArithmeticalStructure (coconutTree (p + 1) s) x.1 x.2) (i : Fin (p + 1))
    (hi : i.val < p) (hd : x.1 (.inl i) = 1) :
    IsArithmeticalStructure (coconutTree p s) (coconutSmoothPath i x).1 (coconutSmoothPath i x).2

/-- **Smoothing a leaf preserves arithmetical structures.** Let $p$ and $s$ be natural numbers
with $p + s \ge 2$, let $(d, r)$ be an arithmetical structure on the coconut tree
$CT(p, s + 1)$, and let $\ell$ be a leaf with $d(\ell) = 1$. Then the labelings $(d', r')$
obtained by smoothing $(d, r)$ at $\ell$ form an arithmetical structure on $CT(p, s)$.

The hypothesis $p + s \ge 2$ excludes the single-edge tree $CT(1, 1)$: there $d = r = (1, 1)$,
and smoothing the leaf gives $d' = 0$ at the remaining vertex, which is not an arithmetical
structure.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 3.6
(`integers-2025-A82-prop-2`). -/
public theorem_wanted IsArithmeticalStructure.coconutSmoothLeaf {p s : ℕ} (hps : 2 ≤ p + s)
    {x : (Fin p ⊕ Fin (s + 1) → ℕ) × (Fin p ⊕ Fin (s + 1) → ℕ)}
    (hx : IsArithmeticalStructure (coconutTree p (s + 1)) x.1 x.2) (l : Fin (s + 1))
    (hd : x.1 (.inr l) = 1) :
    IsArithmeticalStructure (coconutTree p s) (coconutSmoothLeaf l x).1 (coconutSmoothLeaf l x).2

/-- **Subdivision preserves arithmetical structures on coconut trees.** If $(d, r)$ is an
arithmetical structure on the coconut tree $CT(p, s)$, whose path vertices are $v_1, \dots, v_p$,
then for every $1 \le k \le p$, subdividing $(d, r)$ at position $k$ (inserting a new path vertex
just before $v_k$) gives an arithmetical structure on $CT(p + 1, s)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 3.11
(`integers-2025-A82-prop-3`). -/
public theorem_wanted IsArithmeticalStructure.coconutSubdivide {p s : ℕ}
    {x : (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ)}
    (hx : IsArithmeticalStructure (coconutTree p s) x.1 x.2) (i : Fin p) :
    IsArithmeticalStructure (coconutTree (p + 1) s) (coconutSubdivide i x).1
      (coconutSubdivide i x).2

/-- **Unique smooth ancestor.** Let $s \ge 1$ and let $(d, r)$ be an arithmetical structure on the
coconut tree $CT(p, s)$ with $d(\ell_j) \ge 2$ at every leaf $\ell_j$. Then there is exactly one
pair consisting of a number $q$ with $1 \le q \le p$ and a smooth arithmetical structure on
$CT(q, s)$ that is a coconut ancestor of $(d, r)$, that is, one obtained from $(d, r)$ by a
possibly empty sequence of smoothings, each performed at a vertex whose current $d$-label is $1$
and which is either a leaf or a path vertex other than the last path vertex (the one adjacent to
the leaves).

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Lemma 3.8
(`integers-2025-A82-lem-4`). -/
public theorem_wanted IsArithmeticalStructure.existsUnique_smooth_coconutAncestor {p s : ℕ}
    (hs : 1 ≤ s) {x : (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ)}
    (hx : IsArithmeticalStructure (coconutTree p s) x.1 x.2) (hleaf : ∀ j, 2 ≤ x.1 (.inr j)) :
    ∃! y : Σ q : ℕ, (Fin q ⊕ Fin s → ℕ) × (Fin q ⊕ Fin s → ℕ),
      1 ≤ y.1 ∧ y.1 ≤ p ∧ IsSmoothCoconut y.1 s y.2.1 y.2.2 ∧ CoconutAncestor p s x y.1 s y.2

/-- **Number of descendants of a smooth coconut structure.** Let $s \ge 2$ and $1 \le i \le p$,
and let $(d, r)$ be a smooth arithmetical structure on the coconut tree $\mathrm{CT}(i, s)$. Then
exactly $B(p - 1, p - i)$ arithmetical structures on $\mathrm{CT}(p, s)$ are descendants of
$(d, r)$, where $B(n, k)$ is the ballot number.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 4.5
(`integers-2025-A82-prop-4`). -/
public theorem_wanted ncard_coconutDescendants {p s i : ℕ} (hs : 2 ≤ s) (hi : 1 ≤ i)
    (hip : i ≤ p) {y : (Fin i ⊕ Fin s → ℕ) × (Fin i ⊕ Fin s → ℕ)}
    (hy : IsSmoothCoconut i s y.1 y.2) :
    Set.ncard {x : (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ) |
      IsArithmeticalStructure (coconutTree p s) x.1 x.2 ∧ CoconutAncestor p s x i s y}
      = ballotNumber (p - 1) (p - i)

/-- **Counting coconut structures whose leaves cannot be smoothed.** For $p \ge 1$ and $s \ge 2$,
the number of arithmetical structures $(d, r)$ on the coconut tree $CT(p, s)$ with $d(\ell_j) \ge 2$
at every leaf $\ell_j$ is
$$\sum_{i=1}^{p} B(p - 1, p - i)\, N(i),$$
where $B(n, k)$ is the ballot number and $N(i)$ is the number of smooth arithmetical structures on
$CT(i, s)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 4.6
(`integers-2025-A82-cor-1`). -/
public theorem_wanted ncard_arithmeticalStructure_coconutTree_leaves_ge_two {p s : ℕ}
    (hp : 1 ≤ p) (hs : 2 ≤ s) :
    Set.ncard {x : (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ) |
      IsArithmeticalStructure (coconutTree p s) x.1 x.2 ∧ ∀ j, 2 ≤ x.1 (.inr j)}
      = ∑ i ∈ Finset.Icc 1 p, ballotNumber (p - 1) (p - i) *
          Set.ncard {z : (Fin i ⊕ Fin s → ℕ) × (Fin i ⊕ Fin s → ℕ) | IsSmoothCoconut i s z.1 z.2}

end

end MetaMathlibExt
