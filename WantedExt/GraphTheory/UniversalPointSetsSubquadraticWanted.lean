/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Universal point sets of subquadratic size for planar graphs
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import MathlibExt.Combinatorics.SimpleGraph.Planarity

@[expose] public section

namespace MathlibExt.GraphTheory.UniversalPointSetsSubquadraticWanted

/-! Source record `GRAPH-022`. -/

namespace UPSS

/-!
# Clause inventory for [GRAPH-022]

- Quantifier domain: planar graphs (straight-line crossing-free
  embeddable) on `Fin n` vertices.
- Object: plane point sets (`Finset (ℝ × ℝ)`).
- Object: straight-line embeddings (injective, crossing-free, no
  vertex on a non-incident edge).
- Question: subquadratic-size universal point sets exist
  (`f n / n^2 → 0` with `P.card ≤ f n`).
-/

/-- **Straight-line planar embedding.** A map $p$ from the vertex set of a simple graph $G$ to
$\mathbb{R}^2$ is a crossing-free straight-line embedding of $G$ if $p$ is injective, the closed
segments $[p(u), p(v)]$ and $[p(x), p(y)]$ of any two different edges $uv$ and $xy$ meet only in
points $p(z)$ with $z$ an endpoint of both edges, and no vertex $w$ other than $u$ and $v$ has
$p(w)$ on the segment $[p(u), p(v)]$ of an edge $uv$. -/
def IsStraightLinePlanarEmbedding {V : Type} (G : SimpleGraph V)
    (pos : V → ℝ × ℝ) : Prop :=
  Function.Injective pos ∧
  (∀ u v x y : V, G.Adj u v → G.Adj x y →
    (u ≠ x ∨ v ≠ y) → (u ≠ y ∨ v ≠ x) →
    ∀ p : ℝ × ℝ, p ∈ SimpleGraph.Segment (pos u) (pos v) →
      p ∈ SimpleGraph.Segment (pos x) (pos y) →
      ∃ z : V, (z = u ∨ z = v) ∧ (z = x ∨ z = y) ∧ p = pos z) ∧
  (∀ u v w : V, G.Adj u v → w ≠ u → w ≠ v →
    pos w ∉ SimpleGraph.Segment (pos u) (pos v))

/-- **Universal point set for planar graphs.** A finite set $P \subseteq \mathbb{R}^2$ is
universal for $n$-vertex planar graphs if every straight-line planar simple graph $G$ on the
vertex set $\{0, \dots, n-1\}$ has a crossing-free straight-line embedding $p$ with $p(v) \in P$
for every vertex $v$. -/
def IsUniversalPointSet (P : Finset (ℝ × ℝ)) (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), SimpleGraph.IsPlanar G →
    ∃ pos : Fin n → ℝ × ℝ,
      IsStraightLinePlanarEmbedding G pos ∧ ∀ v, pos v ∈ P

/-- **Subquadratic universal point sets.** The statement that there is a function
$f : \mathbb{N} \to \mathbb{N}$ with $f(n)/n^2 \to 0$ as $n \to \infty$ such that for every $n$
some finite set of at most $f(n)$ points of $\mathbb{R}^2$ is a universal point set for
$n$-vertex planar graphs. -/
def ExistsSubquadraticUniversalPointSet : Prop :=
  ∃ f : ℕ → ℕ,
    Filter.Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ) ^ 2) Filter.atTop (nhds 0) ∧
    ∀ n, ∃ P : Finset (ℝ × ℝ), P.card ≤ f n ∧ IsUniversalPointSet P n

end UPSS

/--
**Planar graphs have subquadratic universal point sets.** There is a function
$f : \mathbb{N} \to \mathbb{N}$ with $f(n)/n^2 \to 0$ as $n \to \infty$ such that for every $n$
some finite set $P$ of at most $f(n)$ points of $\mathbb{R}^2$ is a universal point set for
$n$-vertex planar graphs: every straight-line planar simple graph on the vertex set
$\{0, \dots, n-1\}$ has a crossing-free straight-line embedding with all its vertices in $P$.

Taylor Gordon (Theorem 1 of the cited preprint) constructs universal point sets of size
$n \exp(O(\sqrt{\log n}))$ for $n$-vertex planar graphs, using small superpatterns and the
reduction of Bannister, Cheng, Devanny and Eppstein.

Source: Taylor Gordon, Almost Linear Universal Point Sets for Planar
Graphs, arXiv preprint (2026), arXiv:2609.10916, https://arxiv.org/abs/2609.10916; Michael J.
Bannister, Zhanpeng Cheng, William E. Devanny and David Eppstein, Superpatterns and Universal
Point Sets, arXiv:1308.0403, https://arxiv.org/abs/1308.0403. Moved from
`OpenConjectures/GraphTheory/UniversalPointSetsSubquadratic`.
-/
public theorem_wanted ExistsSubquadraticUniversalPointSet_holds : UPSS.ExistsSubquadraticUniversalPointSet

end MathlibExt.GraphTheory.UniversalPointSetsSubquadraticWanted
