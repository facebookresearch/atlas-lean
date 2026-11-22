/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Three-chromatic (0,2)-graphs
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.Combinatorics.ThreeChromaticZeroTwoGraphWanted

/-! UnsolvedMath record `OPG-562`.

The problem-page discussion notes that infinite three-chromatic `(0,2)`-graphs
are easy to construct; the open question concerns finite graphs, represented
here by the vertex type `Fin n`.
-/

/-- **$(0,2)$-graphs.** For a natural number $n$, a simple graph $G$ on the vertex set
$\{0, \dots, n-1\}$ is a $(0,2)$-graph when every two distinct vertices of $G$ have either
exactly zero or exactly two common neighbors. -/
def IsZeroTwo {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ u v : Fin n, u ≠ v →
    (G.commonNeighbors u v).ncard = 0 ∨
      (G.commonNeighbors u v).ncard = 2

/-- **The three-chromatic $(0,2)$-graph conjecture.** It asserts that there are a natural number
$n$ and a simple graph $G$ on the vertex set $\{0, \dots, n-1\}$ in which every two distinct
vertices have either zero or two common neighbors, such that the chromatic number of $G$ is $3$.
-/
noncomputable def conjecture : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    IsZeroTwo G ∧ G.chromaticNumber = 3

/--
**No finite $(0,2)$-graph has chromatic number three.** For every natural number $n$ and
every simple graph $G$ on the vertex set $\{0, \dots, n-1\}$ in which every two distinct vertices
have either zero or two common neighbors, the chromatic number of $G$ is not $3$. In particular,
the three-chromatic $(0,2)$-graph conjecture is false.

Williamson proves the stronger statement that every finite three-colourable $(0,2)$-graph is
bipartite (Theorem 2 of the source below).

Source: Christopher Williamson, Finite
Three-Colourable (0,2)-Graphs Are Bipartite, arXiv preprint (2026), arXiv:2607.10125,
https://arxiv.org/abs/2607.10125. Moved from
`OpenConjectures/Combinatorics/ThreeChromaticZeroTwoGraph`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.ThreeChromaticZeroTwoGraphWanted
