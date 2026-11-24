/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.Rank
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sum-free sets in abelian groups

Statements from Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian
Groups*, INTEGERS 26 (2026), Article A97 (arXiv:2506.17401; definitions taken from the arXiv
TeX source): counts of maximal (distinct) sum-free sets, the container and structure lemmas
the paper quotes, subgroup-counting lemmas, and the quoted bounds on the number of maximal
independent sets in graphs.

A *Schur triple* is `x + y = z`; it is *distinct* when `x, y, z` are pairwise distinct. The
paper's decompositions `G = ℤ_{2^{α₁}} ⊕ … ⊕ K` are written as explicit products.
-/

namespace MetaMathlibExt

@[expose] public section

open Filter

/-- **Sum-free set.** Let $G$ be a set with an addition. A subset $S \subseteq G$ is sum-free if
$x + y \notin S$ for all $x, y \in S$, where $x = y$ is allowed; that is, $S$ contains no Schur
triple $x + y = z$ with $x, y, z \in S$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, introduction. -/
public def IsSumFreeSet {G : Type*} [Add G] (S : Set G) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x + y ∉ S

/-- **Distinct sum-free sets.** Let $G$ be a set with an addition. A subset $S \subseteq G$ is
distinct sum-free if there are no pairwise distinct $x, y, z \in S$ with $x + y = z$, that is, if
$S$ contains no distinct Schur triple.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, introduction. -/
public def IsDistinctSumFreeSet {G : Type*} [Add G] (S : Set G) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ≠ x → x + y ≠ y → x + y ∉ S

/-- **Sum-free sets are distinct sum-free.** For every set $G$ with an addition, every sum-free
subset of $G$ is distinct sum-free.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, introduction. -/
public theorem IsSumFreeSet.isDistinctSumFreeSet {G : Type*} [Add G] {S : Set G}
    (h : IsSumFreeSet S) : IsDistinctSumFreeSet S :=
  fun x hx y hy _ _ _ => h x hx y hy

/-- **The empty set is sum-free.** For every set $G$ with an addition, the empty subset of $G$ is
sum-free.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, introduction. -/
public theorem isSumFreeSet_empty {G : Type*} [Add G] : IsSumFreeSet (∅ : Set G) :=
  fun _ hx => hx.elim

/-- **Size of a largest sum-free subset.** Let $G$ be a set with an addition and $S \subseteq G$.
Write $\mu(S)$ for the supremum in $\mathbb{N}$ of the sizes of the finite sum-free subsets of
$S$ (sets $T$ with $x + y \notin T$ for all $x, y \in T$), taken to be $0$ if these sizes are
unbounded. For finite $S$ this is the largest size of a sum-free subset of $S$, and $\mu(G)$ is
the value for $S = G$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, introduction (`μ(G)`) and Theorem 2. -/
public noncomputable def largestSumFreeCard {G : Type*} [Add G] (S : Set G) : ℕ :=
  sSup {k | ∃ T : Finset G, (T : Set G) ⊆ S ∧ IsSumFreeSet (T : Set G) ∧ T.card = k}

/-- **Trivial bound on sum-free subsets.** Let $G$ be a set with an addition. For every finite
subset $S \subseteq G$, the largest size of a sum-free subset of $S$ is at most $|S|$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, introduction. -/
public theorem largestSumFreeCard_le {G : Type*} [Add G] (S : Finset G) :
    largestSumFreeCard (S : Set G) ≤ S.card := by
  refine csSup_le' ?_
  rintro k ⟨T, hT, -, rfl⟩
  exact Finset.card_le_card (Finset.coe_subset.1 hT)

/-- **Number of maximal sum-free sets.** For a set $G$ with an addition, $f_{\max}(G)$ is the
number of maximal sum-free subsets of $G$, that is, of sets $S \subseteq G$ with $x + y \notin S$
for all $x, y \in S$ (including $x = y$) that are not properly contained in another such set;
it is $0$ if there are infinitely many.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, introduction. -/
public noncomputable def maxSumFreeCount (G : Type*) [Add G] : ℕ :=
  {S : Set G | Maximal IsSumFreeSet S}.ncard

/-- **Number of maximal distinct sum-free sets.** Let $G$ be a set with an addition. The number
$f^*_{\max}(G)$ is the number of subsets of $G$ that are maximal, with respect to inclusion, among
the distinct sum-free subsets of $G$, and it is $0$ if there are infinitely many such subsets.
Here $S \subseteq G$ is distinct sum-free if $x + y \notin S$ for all $x, y \in S$ such that $x$,
$y$ and $x + y$ are pairwise distinct.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, section "Maximal distinct sum-free subsets". -/
public noncomputable def maxDistinctSumFreeCount (G : Type*) [Add G] : ℕ :=
  {S : Set G | Maximal IsDistinctSumFreeSet S}.ncard

/-- **Number of distinct Schur triples.** For a subset $F$ of a set $G$ with an addition, this is
the number of ordered pairs $(x, y)$ with $x, y \in F$ such that $x$, $y$ and $x + y$ are pairwise
distinct and $x + y \in F$, that is, the number of ordered distinct Schur triples $(x, y, x + y)$
in $F$. If there are infinitely many such pairs, the value is $0$ by convention.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, introduction and Lemma 1. -/
public noncomputable def distinctSchurTripleCount {G : Type*} [Add G] (F : Set G) : ℕ :=
  {xy : G × G | xy.1 ∈ F ∧ xy.2 ∈ F ∧ xy.1 ≠ xy.2 ∧ xy.1 + xy.2 ≠ xy.1 ∧
    xy.1 + xy.2 ≠ xy.2 ∧ xy.1 + xy.2 ∈ F}.ncard

/-- **Groups of type I(p).** Let $G$ be a finite set and $p$ a natural number. $G$ is of type
$\mathrm{I}(p)$ if $p$ is the smallest prime with $p \equiv 2 \pmod 3$ dividing $|G|$: that is,
$p$ is prime, $p \equiv 2 \pmod 3$, $p$ divides $|G|$, and $p \le q$ for every prime $q$ with
$q \equiv 2 \pmod 3$ that divides $|G|$.

Only the order of $G$ is used; in the paper $G$ is a finite abelian group.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Definition 1. -/
public def IsTypeOneGroup (G : Type*) [Fintype G] (p : ℕ) : Prop :=
  p.Prime ∧ p % 3 = 2 ∧ p ∣ Fintype.card G ∧
    ∀ q : ℕ, q.Prime → q % 3 = 2 → q ∣ Fintype.card G → p ≤ q

/-- **Characterization of type I(p).** Let $G$ be a finite set and $p$ a natural number. Then $G$
is of type $\mathrm{I}(p)$ if and only if $p$ is prime, $p \equiv 2 \pmod 3$, $p$ divides $|G|$,
and $p \le q$ for every prime $q$ with $q \equiv 2 \pmod 3$ that divides $|G|$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Definition 1. -/
public theorem isTypeOneGroup_iff (G : Type*) [Fintype G] (p : ℕ) :
    IsTypeOneGroup G p ↔ p.Prime ∧ p % 3 = 2 ∧ p ∣ Fintype.card G ∧
      ∀ q : ℕ, q.Prime → q % 3 = 2 → q ∣ Fintype.card G → p ≤ q :=
  Iff.rfl

/-- **Diananda–Yap and Green–Ruzsa theorem.** Let $G$ be a finite abelian group of order $n$, and
let $\mu(G)$ be the largest size of a sum-free subset of $G$. If $G$ is of type $\mathrm{I}(p)$
for a natural number $p$, then $\mu(G) = n\left(\frac{1}{3} + \frac{1}{3p}\right)$. If no prime
$q \equiv 2 \pmod 3$ divides $n$ and $3 \mid n$ (type $\mathrm{II}$), then $\mu(G) = n/3$. If no
prime $q \equiv 2 \pmod 3$ divides $n$ and $3 \nmid n$ (type $\mathrm{III}$), then
$\mu(G) = n\left(\frac{1}{3} - \frac{1}{3m}\right)$, where $m$ is the exponent of $G$.

The paper quotes this result from Diananda–Yap and Green–Ruzsa.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Theorem 1 (`integers-2026-A97-thm-1`), with Definition 1. -/
public theorem_wanted largestSumFreeCard_univ_eq {G : Type*} [AddCommGroup G] [Fintype G] :
    (∀ p, IsTypeOneGroup G p →
      (largestSumFreeCard (Set.univ : Set G) : ℚ) = Fintype.card G * (1 / 3 + 1 / (3 * p))) ∧
    ((∀ q : ℕ, q.Prime → q % 3 = 2 → ¬ q ∣ Fintype.card G) → 3 ∣ Fintype.card G →
      (largestSumFreeCard (Set.univ : Set G) : ℚ) = Fintype.card G / 3) ∧
    ((∀ q : ℕ, q.Prime → q % 3 = 2 → ¬ q ∣ Fintype.card G) → ¬ 3 ∣ Fintype.card G →
      (largestSumFreeCard (Set.univ : Set G) : ℚ) =
        Fintype.card G * (1 / 3 - 1 / (3 * AddMonoid.exponent G)))

/-- **Number of maximal independent sets.** For a graph $\Gamma$, $\mathrm{mis}(\Gamma)$ is the
number of maximal independent sets of $\Gamma$, that is, of sets of pairwise non-adjacent
vertices that are not properly contained in another such set; it is $0$ if there are
infinitely many.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, subsection "Maximal independent sets in graphs". -/
public noncomputable def maxIndepSetCount {V : Type*} (Γ : SimpleGraph V) : ℕ :=
  {I : Set V | Maximal Γ.IsIndepSet I}.ncard

/-- **Edges of the distinct link graph.** Let $G$ be a set with an addition and $S \subseteq G$.
Two elements $x, y \in G$ are adjacent in the distinct link graph of $S$ if $x \ne y$ and there
is some $s \in S$, different from both $x$ and $y$, with $x + y = s$, $x + s = y$ or $y + s = x$.
In an abelian group this says exactly that $\{x, y, s\}$ is a distinct Schur triple for some
$s \in S$. In the paper's graph $L^*_S[B]$ with vertex set $B$, these are the edges between
distinct vertices; the relation itself does not depend on $B$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Definition 2 (i). -/
public def DistinctLinkAdj {G : Type*} [Add G] (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ ∃ s ∈ S, x ≠ s ∧ y ≠ s ∧ (x + y = s ∨ x + s = y ∨ y + s = x)

/-- **Loops of the distinct link graph.** Let $G$ be a set with an addition and $S \subseteq G$.
An element $x \in G$ carries a loop in the distinct link graph of $S$ if there are distinct
$s, s' \in S$, both different from $x$, with $s + s' = x$, $x + s = s'$ or $x + s' = s$. In an
abelian group this says exactly that $\{x, s, s'\}$ is a distinct Schur triple for some distinct
$s, s' \in S$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Definition 2 (ii). -/
public def DistinctLinkLoop {G : Type*} [Add G] (S : Set G) (x : G) : Prop :=
  ∃ s ∈ S, ∃ s' ∈ S, s ≠ s' ∧ x ≠ s ∧ x ≠ s' ∧ (s + s' = x ∨ x + s = s' ∨ x + s' = s)

/-- **Independent sets of the distinct link graph.** Let $G$ be a set with an addition and let
$S, B, I \subseteq G$. The set $I$ is an independent set of the distinct link graph $L^*_S[B]$
(the graph on vertex set $B$ given by the edges and loops of the distinct link graph of $S$) if
$I \subseteq B$, no element of $I$ carries a loop, and no two elements of $I$ are adjacent.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Definition 2. -/
public def IsDistinctLinkIndep {G : Type*} [Add G] (S B I : Set G) : Prop :=
  I ⊆ B ∧ (∀ x ∈ I, ¬DistinctLinkLoop S x) ∧ ∀ x ∈ I, ∀ y ∈ I, ¬DistinctLinkAdj S x y

/-- **The empty set is independent in the distinct link graph.** For every set $G$ with an
addition and all $S, B \subseteq G$, the empty set is an independent set of the distinct link
graph $L^*_S[B]$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Definition 2. -/
public theorem isDistinctLinkIndep_empty {G : Type*} [Add G] (S B : Set G) :
    IsDistinctLinkIndep S B ∅ :=
  ⟨Set.empty_subset B, fun _ hx => hx.elim, fun _ hx => hx.elim⟩

/-- **Container lemma.** For every real $\delta > 0$ there is a natural number $n_0$ such that
every finite abelian group $G$ of order $n \ge n_0$ has a family $\mathcal{F}$ of subsets of $G$
with the following properties: (i) each $F \in \mathcal{F}$ contains at most $\delta n^2$ ordered
distinct Schur triples $(x, y, x + y)$; (ii) every distinct sum-free subset of $G$ is contained
in some $F \in \mathcal{F}$; (iii) $|\mathcal{F}| \le 2^{\delta n}$; (iv) every
$F \in \mathcal{F}$ is of the form $A \cup B$ with $A$ sum-free and $|B| \le \delta n$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 1 (`integers-2026-A97-lem-1`). -/
public theorem_wanted exists_distinct_sumFree_containers (δ : ℝ) (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ (G : Type) [AddCommGroup G] [Fintype G], n₀ ≤ Fintype.card G →
      ∃ 𝓕 : Set (Set G),
        (∀ F ∈ 𝓕, (distinctSchurTripleCount F : ℝ) ≤ δ * (Fintype.card G : ℝ) ^ 2) ∧
        (∀ S : Set G, IsDistinctSumFreeSet S → ∃ F ∈ 𝓕, S ⊆ F) ∧
        (𝓕.ncard : ℝ) ≤ (2 : ℝ) ^ (δ * Fintype.card G) ∧
        ∀ F ∈ 𝓕, ∃ A B : Set G, F = A ∪ B ∧ IsSumFreeSet A ∧
          (B.ncard : ℝ) ≤ δ * Fintype.card G

/-- **Green–Ruzsa structure lemma.** Let $G$ be a finite abelian group of type $\mathrm{I}(p)$ and
let $k$ be a natural number with $p = 3k + 2$. If $A \subseteq G$ is sum-free and
$|A| > \left(\frac{1}{3} + \frac{1}{3(p + 1)}\right)|G|$, then there is a group homomorphism
$\psi : G \to \mathbb{Z}_p$ with $\psi(a) \in \{k + 1, \dots, 2k + 1\}$ for every $a \in A$,
where $\mathbb{Z}_p$ is identified with $\{0, 1, \dots, p - 1\}$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 2 (`integers-2026-A97-lem-2`). -/
public theorem_wanted exists_addMonoidHom_zmod_of_large_sumFree {G : Type*} [AddCommGroup G]
    [Fintype G] {p k : ℕ} (hG : IsTypeOneGroup G p) (hpk : p = 3 * k + 2) {A : Set G}
    (hA : IsSumFreeSet A)
    (hcard : ((1 : ℝ) / 3 + 1 / (3 * (p + 1))) * Fintype.card G < A.ncard) :
    ∃ ψ : G →+ ZMod p, ∀ a ∈ A, (ψ a).val ∈ Finset.Icc (k + 1) (2 * k + 1)

/-- **Counting subgroups by order and by index.** In a finite abelian group $G$, for every
natural number $k$ the number of subgroups of order $k$ equals the number of subgroups of
index $k$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 3 (`integers-2026-A97-lem-3`). -/
public theorem_wanted ncard_addSubgroup_card_eq_ncard_index_eq (G : Type*) [AddCommGroup G]
    [Finite G] (k : ℕ) :
    {H : AddSubgroup G | Nat.card H = k}.ncard = {H : AddSubgroup G | H.index = k}.ncard

/-- **Ranks of the index-two subgroups of a finite abelian 2-group.** Let $r_1, r_2$ be natural
numbers with $r = r_1 + r_2 \ge 1$, let $\alpha_1, \dots, \alpha_{r_1} \ge 2$, and let
$G = \mathbb{Z}_{2^{\alpha_1}} \oplus \dots \oplus \mathbb{Z}_{2^{\alpha_{r_1}}} \oplus
\mathbb{Z}_2^{r_2}$. Then exactly $2^{r_1} - 1$ subgroups of $G$ of index $2$ have rank $r$,
and exactly $2^r - 2^{r_1}$ subgroups of $G$ of index $2$ have rank $r - 1$, where the rank
of a group is the minimal number of its generators.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 4 (`integers-2026-A97-lem-4`). -/
public theorem_wanted ncard_index_two_addSubgroup_rank (r₁ r₂ : ℕ) (hr : 1 ≤ r₁ + r₂)
    (α : Fin r₁ → ℕ) (hα : ∀ i, 2 ≤ α i) :
    {H : AddSubgroup (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2)) |
        H.index = 2 ∧ AddGroup.rank H = r₁ + r₂}.ncard = 2 ^ r₁ - 1 ∧
      {H : AddSubgroup (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2)) |
        H.index = 2 ∧ AddGroup.rank H = r₁ + r₂ - 1}.ncard = 2 ^ (r₁ + r₂) - 2 ^ r₁

/-- **Balogh–Liu–Sharifzadeh–Treglown bound.** Let $k \ge 1$ be a real number and let $\Gamma$
be a finite graph with $n$ vertices, minimum degree $\delta(\Gamma)$ and maximum degree
$\Delta(\Gamma) \le k\,\delta(\Gamma)$, and put $b = \sqrt{\delta(\Gamma)}$. Then the number
$\mathrm{mis}(\Gamma)$ of maximal independent sets of $\Gamma$ satisfies
$\mathrm{mis}(\Gamma) \le \bigl(\sum_{0 \le i \le n/b} \binom{n}{i}\bigr) \cdot
3^{\frac{k}{k+1} \cdot \frac{n}{3} + \frac{2n}{3b}}$, where $n/b$ and $2n/(3b)$ are read as $0$
when $\delta(\Gamma) = 0$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 5 (`integers-2026-A97-lem-5`). -/
public theorem_wanted maxIndepSetCount_le_of_maxDegree_le {V : Type*} [Fintype V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] {k : ℝ} (hk : 1 ≤ k)
    (hΔ : (Γ.maxDegree : ℝ) ≤ k * Γ.minDegree) :
    (maxIndepSetCount Γ : ℝ) ≤
      (∑ i ∈ Finset.range (⌊(Fintype.card V : ℝ) / Real.sqrt Γ.minDegree⌋₊ + 1),
          ((Fintype.card V).choose i : ℝ)) *
        (3 : ℝ) ^ (k / (k + 1) * (Fintype.card V / 3) +
          2 * Fintype.card V / (3 * Real.sqrt Γ.minDegree))

/-- **Almost triangle-free bound.** Let $\Gamma$ be a finite graph, let $T$ be a set of vertices
of $\Gamma$, let $n \ge 1$ and $D \ge 1$ be integers, and let $k$ be a real number. Suppose
that the graph $\Gamma'$ obtained from $\Gamma$ by deleting $T$ is triangle-free, has $n$
vertices and has at least $n/2 + k$ edges, and that $\Gamma$ has maximum degree
$\Delta(\Gamma) \le D$. Then the number $\mathrm{mis}(\Gamma)$ of maximal independent sets of
$\Gamma$ satisfies $\mathrm{mis}(\Gamma) \le 2^{n/2 - k/(100D^2) + 2|T|}$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 6 (`integers-2026-A97-lem-6`). -/
public theorem_wanted maxIndepSetCount_le_of_almost_triangleFree {V : Type*} [Fintype V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (T : Finset V) {n D : ℕ} (hn : 1 ≤ n)
    (hD : 1 ≤ D) (k : ℝ)
    (htri : ∀ a b c : V, a ∉ T → b ∉ T → c ∉ T → ¬(Γ.Adj a b ∧ Γ.Adj b c ∧ Γ.Adj a c))
    (hΔ : Γ.maxDegree ≤ D) (hv : Fintype.card V - T.card = n)
    (he : (n : ℝ) / 2 + k ≤ {e ∈ Γ.edgeSet | ∀ v ∈ e, v ∉ T}.ncard) :
    (maxIndepSetCount Γ : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2 - k / (100 * (D : ℝ) ^ 2) + 2 * T.card)

/-- **Liu–Sharifzadeh stability bound.** Let $\Gamma$ be a graph with $n$ vertices, $n + k$
edges for an integer $k$, and maximum degree $\Delta \ge 1$. Then the number
$\mathrm{mis}(\Gamma)$ of maximal independent sets of $\Gamma$ satisfies
$\mathrm{mis}(\Gamma) \le 3^{\Delta/13} \cdot 3^{n/3 - k/(13\Delta)}$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 7 (`integers-2026-A97-lem-7`). -/
public theorem_wanted maxIndepSetCount_le_of_edge_count {V : Type*} [Fintype V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (k : ℤ) {Δ : ℕ} (hΔpos : 1 ≤ Δ)
    (hΔ : Γ.maxDegree = Δ) (he : (Γ.edgeFinset.card : ℤ) = Fintype.card V + k) :
    (maxIndepSetCount Γ : ℝ) ≤
      (3 : ℝ) ^ ((Δ : ℝ) / 13) * (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3 - k / (13 * Δ))

/-- **Link-graph extension lemma.** Let $G$ be an abelian group and let $B, S \subseteq G$ be
disjoint distinct sum-free sets. If $I \subseteq B$ and $S \cup I$ is a maximal distinct
sum-free subset of $G$, then $I$ is a maximal independent set of the distinct link graph
$L^*_S[B]$: a subset of $B$ with no looped vertex and no two adjacent vertices that is not
properly contained in another such set.

Disjointness of $B$ and $S$ is needed: for $G = \mathbb{Z}_2$, $S = G$, $B = \{0\}$ and
$I = \emptyset$ the conclusion fails.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 8 (`integers-2026-A97-lem-8`). -/
public theorem_wanted maximal_isDistinctLinkIndep_of_maximal {G : Type*} [AddCommGroup G]
    {B S I : Set G} (hB : IsDistinctSumFreeSet B) (hS : IsDistinctSumFreeSet S)
    (hBS : Disjoint B S) (hI : I ⊆ B) (hmax : Maximal IsDistinctSumFreeSet (S ∪ I)) :
    Maximal (IsDistinctLinkIndep S B) I

/-- **Maximal distinct sum-free sets in groups of type $I(p)$.** Let $G$ be a finite abelian
group and let $p \ge 5$ be such that $G$ is of type $I(p)$, that is, $p$ is the smallest prime
with $p \equiv 2 \pmod 3$ that divides $|G|$. Call $S \subseteq G$ sum-free if $x + y \notin S$
for all $x, y \in S$, and distinct sum-free if $x + y \notin S$ for all $x, y \in S$ such that
$x$, $y$ and $x + y$ are pairwise distinct. Let $\mu(G)$ be the size of a largest sum-free subset
of $G$, and let $f^*_{\max}(G)$ be the number of maximal distinct sum-free subsets of $G$. Then
$f^*_{\max}(G) \ge 2^{\mu(G)/2}$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Proposition 1 (`integers-2026-A97-prop-1`). -/
public theorem_wanted two_rpow_le_maxDistinctSumFreeCount_of_typeOne {G : Type*}
    [AddCommGroup G] [Fintype G] {p : ℕ} (hp : 5 ≤ p) (hG : IsTypeOneGroup G p) :
    (2 : ℝ) ^ ((largestSumFreeCard (Set.univ : Set G) : ℝ) / 2) ≤ maxDistinctSumFreeCount G

/-- **Random sum-free sets.** For a finite abelian group $G$ let $\mu(G)$ be the size of a
largest sum-free subset of $G$. Let $(G_n)_{n \ge 0}$ be finite abelian groups with
$|G_i| < |G_j|$ and $\mu(G_i)/|G_i| = \mu(G_j)/|G_j|$ whenever $i < j$. Then for every
$\varepsilon > 0$ there is $C > 0$ such that for every real sequence $(p_n)$ with
$C |G_n|^{-1/2} \le p_n \le 1$ for all $n$, the probability that the largest sum-free subset
of the binomial random subset $G_{n,p_n}$ has size within $\varepsilon \mu(G_n) p_n$ of
$\mu(G_n) p_n$ tends to $1$ as $n \to \infty$. Here $G_{n,p}$ contains each element of $G_n$
independently with probability $p$, so this probability is
$\sum_S p_n^{|S|} (1-p_n)^{|G_n|-|S|}$ over the subsets $S \subseteq G_n$ with that property.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Theorem 2 (`integers-2026-A97-thm-2`). -/
public theorem_wanted tendsto_prob_largestSumFreeCard_random (G : ℕ → Type)
    [∀ n, AddCommGroup (G n)] [∀ n, Fintype (G n)] [∀ n, DecidableEq (G n)]
    (hcard : ∀ i j, i < j → Fintype.card (G i) < Fintype.card (G j))
    (hdens : ∀ i j, i < j →
      (largestSumFreeCard (Set.univ : Set (G i)) : ℝ) / Fintype.card (G i) =
        (largestSumFreeCard (Set.univ : Set (G j)) : ℝ) / Fintype.card (G j))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ → ℝ,
      (∀ n, C * (Fintype.card (G n) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ p n) → (∀ n, p n ≤ 1) →
      Tendsto (fun n => ∑ S : Finset (G n),
          (p n) ^ S.card * (1 - p n) ^ (Fintype.card (G n) - S.card) *
            (if |(largestSumFreeCard (S : Set (G n)) : ℝ) -
                largestSumFreeCard (Set.univ : Set (G n)) * p n| ≤
                ε * largestSumFreeCard (Set.univ : Set (G n)) * p n then 1 else 0))
        atTop (nhds 1)

/-- **Counting maximal sum-free sets in elementary abelian 2- and 3-groups.** Let $f_{\max}(G)$
be the number of maximal sum-free subsets of $G$. As $k \to \infty$, with $n = 2^k$,
$f_{\max}(\mathbb{Z}_2^k) = \bigl(\binom{n-1}{2} + o(1)\bigr) 2^{n/4}$, and with $n = 3^k$,
$f_{\max}(\mathbb{Z}_3^k) = \bigl((n-3)(n-1)/3 + o(1)\bigr) 3^{n/9}$; that is,
$f_{\max}(\mathbb{Z}_2^k)/2^{n/4} - \binom{n-1}{2} \to 0$ and
$f_{\max}(\mathbb{Z}_3^k)/3^{n/9} - (n-3)(n-1)/3 \to 0$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Theorem 3 (`integers-2026-A97-thm-3`). -/
public theorem_wanted maxSumFreeCount_elementary_two_three :
    Tendsto (fun k : ℕ => (maxSumFreeCount (Fin k → ZMod 2) : ℝ) /
        (2 : ℝ) ^ ((2 : ℝ) ^ k / 4) - ((2 ^ k - 1).choose 2 : ℝ)) atTop (nhds 0) ∧
      Tendsto (fun k : ℕ => (maxSumFreeCount (Fin k → ZMod 3) : ℝ) /
        (3 : ℝ) ^ ((3 : ℝ) ^ k / 9) - ((3 : ℝ) ^ k - 3) * ((3 : ℝ) ^ k - 1) / 3)
        atTop (nhds 0)

/-- **Maximal distinct sum-free sets in groups of even order.** Write $f^*_{\max}(G)$ for the
number of maximal distinct sum-free subsets of an abelian group $G$. There is a natural number
$C$ such that for every real $\varepsilon > 0$ there is $n_0$ with the following property. Let
$r \ge 1$, let $\alpha_1, \dots, \alpha_r \ge 1$, let $K$ be a finite abelian group of odd order,
and let $G = \mathbb{Z}_{2^{\alpha_1}} \oplus \dots \oplus \mathbb{Z}_{2^{\alpha_r}} \oplus K$
have order $n$. If $n \ge n_0$ and $n / 2^r \ge C$, then
$2^{(1/4 - \varepsilon) n} \le f^*_{\max}(G) \le 2^{(1/4 + \varepsilon) n}$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Theorem 4 (`integers-2026-A97-thm-4`). -/
public theorem_wanted maxDistinctSumFreeCount_even_order :
    ∃ C : ℕ, ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (r : ℕ) (α : Fin r → ℕ) (K : Type)
      [AddCommGroup K] [Fintype K], 1 ≤ r → (∀ i, 1 ≤ α i) → Odd (Fintype.card K) →
      n₀ ≤ Fintype.card (((i : Fin r) → ZMod (2 ^ α i)) × K) →
      (C : ℝ) ≤ (Fintype.card (((i : Fin r) → ZMod (2 ^ α i)) × K) : ℝ) / 2 ^ r →
      (2 : ℝ) ^ ((1 / 4 - ε) * Fintype.card (((i : Fin r) → ZMod (2 ^ α i)) × K)) ≤
          maxDistinctSumFreeCount (((i : Fin r) → ZMod (2 ^ α i)) × K) ∧
        (maxDistinctSumFreeCount (((i : Fin r) → ZMod (2 ^ α i)) × K) : ℝ) ≤
          (2 : ℝ) ^ ((1 / 4 + ε) * Fintype.card (((i : Fin r) → ZMod (2 ^ α i)) × K))

/-- **Sharp upper bound on maximal distinct sum-free sets.** Write $f^*_{\max}(G)$ for the number
of maximal distinct sum-free subsets of an abelian group $G$. There is a natural number $C$ such
that for every real $\eta > 0$ there is $n_0$ with the following property. Let $r_1, r_2 \ge 0$
with $r = r_1 + r_2 \ge 1$, let $\alpha_1, \dots, \alpha_{r_1} \ge 2$, let $K$ be a finite
abelian group of odd order, and let
$G = \mathbb{Z}_{2^{\alpha_1}} \oplus \dots \oplus \mathbb{Z}_{2^{\alpha_{r_1}}} \oplus
\mathbb{Z}_2^{r_2} \oplus K$ have order $n$. If $n \ge n_0$ and $n / 2^r \ge C$, then
$$f^*_{\max}(G) \le (2^{2r-1} + 2^{r+r_1-1} - 2^{r+1} + 2^{r_1})\, 2^{n/4} +
(2^r - 2^{r_1} + \eta)\, 2^{n/4 - 2^{r-2}}.$$

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Theorem 5 (`integers-2026-A97-thm-5`). -/
public theorem_wanted maxDistinctSumFreeCount_le_sharp :
    ∃ C : ℕ, ∀ η : ℝ, 0 < η → ∃ n₀ : ℕ, ∀ (r₁ r₂ : ℕ) (α : Fin r₁ → ℕ) (K : Type)
      [AddCommGroup K] [Fintype K], 1 ≤ r₁ + r₂ → (∀ i, 2 ≤ α i) → Odd (Fintype.card K) →
      n₀ ≤ Fintype.card (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) →
      (C : ℝ) ≤ (Fintype.card (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) : ℝ) /
        2 ^ (r₁ + r₂) →
      (maxDistinctSumFreeCount
          (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) : ℝ) ≤
        ((2 : ℝ) ^ (2 * (r₁ + r₂) - 1) + 2 ^ (r₁ + r₂ + r₁ - 1) - 2 ^ (r₁ + r₂ + 1) + 2 ^ r₁) *
            (2 : ℝ) ^ ((Fintype.card
              (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) : ℝ) / 4) +
          ((2 : ℝ) ^ (r₁ + r₂) - 2 ^ r₁ + η) *
            (2 : ℝ) ^ ((Fintype.card
              (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) : ℝ) / 4 -
                (2 : ℝ) ^ ((r₁ + r₂ : ℝ) - 2))

/-- **Sharp lower bound on maximal distinct sum-free sets.** Write $f^*_{\max}(G)$ for the number
of maximal distinct sum-free subsets of an abelian group $G$. There is a natural number $C$ such
that for every real $\eta > 0$ there is $n_0$ with the following property. Let $r_1, r_2 \ge 0$
with $r = r_1 + r_2 \ge 1$, let $\alpha_1, \dots, \alpha_{r_1} \ge 2$, let $K$ be a finite
abelian group of odd order, and let
$G = \mathbb{Z}_{2^{\alpha_1}} \oplus \dots \oplus \mathbb{Z}_{2^{\alpha_{r_1}}} \oplus
\mathbb{Z}_2^{r_2} \oplus K$ have order $n$. If $n \ge n_0$ and $n / 2^r \ge C$, then
$$(2^{2r-1} + 2^{r+r_1-1} - 2^{r+1} + 2^{r_1})\, 2^{n/4} +
(2^r - 2^{r_1} - \eta)\, 2^{n/4 - 2^{r-2}} \le f^*_{\max}(G).$$

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Theorem 6 (`integers-2026-A97-thm-6`). -/
public theorem_wanted le_maxDistinctSumFreeCount_sharp :
    ∃ C : ℕ, ∀ η : ℝ, 0 < η → ∃ n₀ : ℕ, ∀ (r₁ r₂ : ℕ) (α : Fin r₁ → ℕ) (K : Type)
      [AddCommGroup K] [Fintype K], 1 ≤ r₁ + r₂ → (∀ i, 2 ≤ α i) → Odd (Fintype.card K) →
      n₀ ≤ Fintype.card (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) →
      (C : ℝ) ≤ (Fintype.card (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) : ℝ) /
        2 ^ (r₁ + r₂) →
      ((2 : ℝ) ^ (2 * (r₁ + r₂) - 1) + 2 ^ (r₁ + r₂ + r₁ - 1) - 2 ^ (r₁ + r₂ + 1) + 2 ^ r₁) *
            (2 : ℝ) ^ ((Fintype.card
              (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) : ℝ) / 4) +
          ((2 : ℝ) ^ (r₁ + r₂) - 2 ^ r₁ - η) *
            (2 : ℝ) ^ ((Fintype.card
              (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) : ℝ) / 4 -
                (2 : ℝ) ^ ((r₁ + r₂ : ℝ) - 2)) ≤
        (maxDistinctSumFreeCount
          (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) : ℝ)

end

end MetaMathlibExt
