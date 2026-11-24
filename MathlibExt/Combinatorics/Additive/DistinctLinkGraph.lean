/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Order.Minimal

/-!
# Distinct link graphs for sum-free sets

We define the edges, loops and independent sets of the distinct link graph of a set. The
link-graph extension lemma is Lemma 8 of Nathanaël Hassler and Andrew Treglown,
*Notes on Sum-Free Sets in Abelian Groups*, INTEGERS 26 (2026), Article A97.
-/

namespace MetaMathlibExt

@[expose] public section

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

/-- **Link-graph extension lemma.** Let $G$ be an abelian group and let $B, S \subseteq G$ be
disjoint distinct sum-free sets. If $I \subseteq B$ and $S \cup I$ is a maximal distinct
sum-free subset of $G$, then $I$ is a maximal independent set of the distinct link graph
$L^*_S[B]$: a subset of $B$ with no looped vertex and no two adjacent vertices that is not
properly contained in another such set.

Disjointness of $B$ and $S$ is needed: for $G = \mathbb{Z}_2$, $S = G$, $B = \{0\}$ and
$I = \emptyset$ the conclusion fails.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 8 (`integers-2026-A97-lem-8`). -/
public theorem maximal_isDistinctLinkIndep_of_maximal {G : Type*} [AddCommGroup G]
    {B S I : Set G} (hB : IsDistinctSumFreeSet B) (hS : IsDistinctSumFreeSet S)
    (hBS : Disjoint B S) (hI : I ⊆ B) (hmax : Maximal IsDistinctSumFreeSet (S ∪ I)) :
    Maximal (IsDistinctLinkIndep S B) I := by
  have noTriple {x y z : G} (hx : x ∈ S ∪ I) (hy : y ∈ S ∪ I) (hz : z ∈ S ∪ I)
      (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) (hadd : x + y = z) : False := by
    subst z
    exact hmax.prop x hx y hy hxy hzx hzy hz
  refine ⟨⟨hI, ?_, ?_⟩, ?_⟩
  · intro x hx
    rintro ⟨s, hs, t, ht, hst, hxs, hxt, h | h | h⟩
    · exact noTriple (Or.inl hs) (Or.inl ht) (Or.inr hx) hst hxs hxt h
    · exact noTriple (Or.inr hx) (Or.inl hs) (Or.inl ht) hxs hxt.symm hst.symm h
    · exact noTriple (Or.inr hx) (Or.inl ht) (Or.inl hs) hxt hxs.symm hst h
  · intro x hx y hy
    rintro ⟨hxy, s, hs, hxs, hys, h | h | h⟩
    · exact noTriple (Or.inr hx) (Or.inr hy) (Or.inl hs) hxy hxs.symm hys.symm h
    · exact noTriple (Or.inr hx) (Or.inl hs) (Or.inr hy) hxs hxy.symm hys h
    · exact noTriple (Or.inr hy) (Or.inl hs) (Or.inr hx) hys hxy hxs h
  · intro J hJ hIJ
    obtain ⟨hJB, hloop, hadj⟩ := hJ
    have hSJ : IsDistinctSumFreeSet (S ∪ J) := by
      intro x hx y hy hxy hzx hzy hz
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz
      · exact hS x hx y hy hxy hzx hzy hz
      · exact hloop (x + y) hz ⟨x, hx, y, hy, hxy, hzx, hzy, Or.inl rfl⟩
      · exact hloop y hy
          ⟨x, hx, x + y, hz, hzx.symm, hxy.symm, hzy.symm, Or.inr (Or.inl (add_comm y x))⟩
      · exact hadj y hy (x + y) hz
          ⟨hzy.symm, x, hx, hxy.symm, hzx, Or.inr (Or.inl (add_comm y x))⟩
      · exact hloop x hx ⟨y, hy, x + y, hz, hzy.symm, hxy, hzx.symm, Or.inr (Or.inl rfl)⟩
      · exact hadj x hx (x + y) hz ⟨hzx.symm, y, hy, hxy, hzy, Or.inr (Or.inl rfl)⟩
      · exact hadj x hx y hy ⟨hxy, x + y, hz, hzx.symm, hzy.symm, Or.inl rfl⟩
      · exact hB x (hJB hx) y (hJB hy) hxy hzx hzy (hJB hz)
    have hsub : S ∪ J ⊆ S ∪ I := hmax.le_of_ge hSJ (Set.union_subset_union_right S hIJ)
    intro x hx
    exact (hsub (Or.inr hx)).resolve_left (Set.disjoint_left.mp hBS (hJB hx))

end

end MetaMathlibExt
