/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.ArithmeticalStructureCoconutCount
public import MathlibExt.Combinatorics.ArithmeticalStructureCoconutSubdivision
public import MathlibExt.Combinatorics.ArithmeticalStructureCoconutTree
public import MathlibExt.Combinatorics.ArithmeticalStructureCoconutTwoLeaves
public import MathlibExt.Combinatorics.ArithmeticalStructureCoconutUnsmoothedLeaves
public import MathlibExt.Combinatorics.ArithmeticalStructureStar
public import MathlibExt.Combinatorics.EuclideanChainLength
public import MathlibExt.Combinatorics.ArithmeticalStructureCoconutTreeCoconutSmoothPath

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

end

end MetaMathlibExt
