/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Batteries.Util.ProofWanted

namespace MetaMathlibExt

@[expose] public section

/-- **Graphs with a $K_5$ minor.** A simple graph $G$ has $K_5$ as a minor if there are five
nonempty, pairwise disjoint sets of vertices $S_1, \dots, S_5$ such that any two vertices in the
same set are joined by a walk in $G$ all of whose vertices lie in that set, and for all distinct
$i, j$ some vertex of $S_i$ is adjacent in $G$ to some vertex of $S_j$.

Together with $K_{3,3}$, this is one of the two forbidden minors for planarity (Wagner,
Kuratowski).

Source: https://en.wikipedia.org/wiki/Four_color_theorem (statement four-color-s1). -/
def HasK5Minor {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ S : Fin 5 → Set V,
    (∀ i, ∃ x, x ∈ S i) ∧
    Pairwise (fun i j => ∀ x, x ∈ S i → x ∈ S j → False) ∧
    (∀ i, ∀ u ∈ S i, ∀ v ∈ S i, ∃ p : G.Walk u v, ∀ w ∈ p.support, w ∈ S i) ∧
    ∀ i j, i ≠ j → ∃ u ∈ S i, ∃ v ∈ S j, G.Adj u v

/-- **Graphs with a $K_{3,3}$ minor.** A simple graph $G$ has $K_{3,3}$ as a minor if there are
six nonempty, pairwise disjoint sets of vertices $L_1, L_2, L_3, R_1, R_2, R_3$ such that any two
vertices in the same set are joined by a walk in $G$ all of whose vertices lie in that set, and
for all $i, j \in \{1, 2, 3\}$ some vertex of $L_i$ is adjacent in $G$ to some vertex of $R_j$.

Together with $K_5$, this is one of the two forbidden minors for planarity (Wagner, Kuratowski).

Source: https://en.wikipedia.org/wiki/Four_color_theorem (statement four-color-s1). -/
def HasK33Minor {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ L R : Fin 3 → Set V,
    (∀ i, ∃ x, x ∈ L i) ∧
    (∀ j, ∃ x, x ∈ R j) ∧
    (∀ i j, ∀ x, x ∈ L i → x ∈ R j → False) ∧
    Pairwise (fun i i' => ∀ x, x ∈ L i → x ∈ L i' → False) ∧
    Pairwise (fun j j' => ∀ x, x ∈ R j → x ∈ R j' → False) ∧
    (∀ i, ∀ u ∈ L i, ∀ v ∈ L i, ∃ p : G.Walk u v, ∀ w ∈ p.support, w ∈ L i) ∧
    (∀ j, ∀ u ∈ R j, ∀ v ∈ R j, ∃ p : G.Walk u v, ∀ w ∈ p.support, w ∈ R j) ∧
    ∀ i j, ∃ u ∈ L i, ∃ v ∈ R j, G.Adj u v

/-- **Planarity by forbidden minors.** A simple graph $G$ is called planar here if it has neither
$K_5$ nor $K_{3,3}$ as a minor.

Without this condition the four color theorem fails: $K_5$ is not 4-colorable.

Source: https://en.wikipedia.org/wiki/Four_color_theorem (statement four-color-s1). -/
def IsPlanar {V : Type} (G : SimpleGraph V) : Prop :=
  ¬ HasK5Minor G ∧ ¬ HasK33Minor G

/-- **Four color theorem.** Let $G$ be a simple graph on a finite vertex set $V$ that has neither
$K_5$ nor $K_{3,3}$ as a minor, and let $\ell$ assign a natural number $\ell(u, v)$ to every
ordered pair of vertices $u, v$ such that $u$ and $v$ are adjacent in $G$ if and only if
$u \ne v$ and $\ell(u, v) > 0$. Then $G$ has a proper vertex coloring with four colors.

Here the vertices stand for the regions of a map and $\ell(u, v)$ for the length of their common
boundary, so regions that meet only at a corner are not adjacent. Without the minor condition the
conclusion fails: $K_5$ needs five colors.

Source: https://en.wikipedia.org/wiki/Four_color_theorem (statement four-color-s1). -/
theorem_wanted fourColorTheorem {V : Type} [Fintype V] (G : SimpleGraph V)
    (planar : IsPlanar G)
    (boundaryLength : V → V → ℕ)
    (adj : ∀ u v, G.Adj u v ↔ u ≠ v ∧ 0 < boundaryLength u v) :
    G.Colorable 4

end

end MetaMathlibExt