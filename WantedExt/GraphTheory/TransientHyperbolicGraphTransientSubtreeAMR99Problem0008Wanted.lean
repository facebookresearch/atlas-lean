/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A transient hyperbolic graph without transient subtrees (Benjamini, Open problem 1.62)

I. Benjamini, Coarse Geometry and Randomness (Saint-Flour lecture notes), Open problem 1.62: show
that a bounded degree transient hyperbolic graph contains a transient subtree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Order.Real

@[expose] public section

namespace MathlibExt.GraphTheory.TransientHyperbolicGraphTransientSubtreeAMR99Problem0008Wanted

/-!
Source: I. Benjamini, Coarse Geometry and Randomness (Saint-Flour lecture notes), Open problem 1.62.
UnsolvedMath record UM-10000008 (`AMR-099-0008`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are connected simple graphs with bounded degree; hyperbolicity is Gromov's four-point
condition `(x | z)_w ≥ min((x | y)_w, (y | z)_w) - δ` for the graph metric (equivalent to thin
triangles for graphs); it is the inequality of MathlibExt's `Metric.IsGromovHyperbolic`, written for
`SimpleGraph.dist` because that predicate needs a `PseudoMetricSpace` instance, which a graph does
not carry. Transience of simple random walk on an infinite graph is the finiteness of the expected
number of returns `∑ₙ pₙ(o, o)`, with `pₙ(o, o)` the sum over closed walks of length `n` at `o` of
`∏ 1/deg`; finite graphs are not transient (on a one-vertex graph the walk sum would see no
returns). A subtree is a subgraph that is a tree, with its own random walk.
-/

/-- The degree of `v`: the cardinality of its neighbour set (finite for bounded-degree graphs). -/
noncomputable def vertexDegree {V : Type*} (G : SimpleGraph V) (v : V) : ℕ :=
  (G.neighborSet v).ncard

/-- The `n`-step return probability of simple random walk on `G` at `o`: the sum over closed walks
of length `n` at `o` of `∏ 1 / deg` over the vertices the walk leaves. -/
noncomputable def returnProb {V : Type*} (G : SimpleGraph V) (o : V) (n : ℕ) : ENNReal :=
  ∑' w : {w : G.Walk o o // w.length = n},
    (w.1.support.dropLast.map fun v => ((vertexDegree G v : ENNReal))⁻¹).prod

/-- Simple random walk on the infinite graph `G` is transient: the expected number of returns to
some vertex, `∑ₙ pₙ(o, o)`, is finite. Finite graphs are excluded: on a one-vertex graph the walk
sum above would count no returns at all, although the walk never leaves its vertex. -/
def IsTransient {V : Type*} (G : SimpleGraph V) : Prop :=
  Infinite V ∧ ∃ o : V, ∑' n, returnProb G o n ≠ ⊤

/-- `G` has bounded degree. -/
def HasBoundedDegree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ D : ℕ, ∀ v, (G.neighborSet v).Finite ∧ (G.neighborSet v).ncard ≤ D

/-- The Gromov product `(x | y)_w = (d(x, w) + d(y, w) - d(x, y)) / 2` for the graph metric. -/
noncomputable def gromovProduct {V : Type*} (G : SimpleGraph V) (x y w : V) : ℝ :=
  ((G.dist x w : ℝ) + G.dist y w - G.dist x y) / 2

/-- `G` is Gromov hyperbolic (four-point condition for the graph metric). -/
def IsGromovHyperbolic {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ δ : ℝ, ∀ x y z w : V,
    min (gromovProduct G x y w) (gromovProduct G y z w) - δ ≤ gromovProduct G x z w

/-- Benjamini's Open Problem 1.62 (Coarse Geometry and Randomness): every bounded-degree transient
hyperbolic graph contains a transient subtree. -/
def transientHyperbolicHasTransientSubtree : Prop :=
  ∀ (V : Type) (G : SimpleGraph V), G.Connected → HasBoundedDegree G → IsGromovHyperbolic G →
    IsTransient G → ∃ H : G.Subgraph, H.coe.IsTree ∧ IsTransient H.coe

/--
Resolved false: Carmesin, Federici and Georgakopoulos constructed a bounded-degree, transient,
Gromov-hyperbolic (even Liouville) graph every subtree of which is recurrent, answering Benjamini's
question in the negative. Source: I. Benjamini, Coarse Geometry and Randomness (Saint-Flour lecture
notes), Open problem 1.62; resolution: J. Carmesin, B. Federici and A. Georgakopoulos, A Liouville
hyperbolic souvlaki, Electron. J. Probab. 22 (2017), no. 36, 1-19, doi:10.1214/17-EJP44,
arXiv:1603.06712, Theorem 6.1 (arXiv numbering): the graph Ψ̄ is a bounded degree transient
Gromov-hyperbolic graph that does not contain a transient subtree; Introduction: "Benjamini [Open
Problem 1.62] asks whether hyperbolicity is such a condition. We answer this in the negative",
https://arxiv.org/abs/1603.06712.
-/
public theorem_wanted transientHyperbolicHasTransientSubtree_refuted :
    ¬ transientHyperbolicHasTransientSubtree

end MathlibExt.GraphTheory.TransientHyperbolicGraphTransientSubtreeAMR99Problem0008Wanted
