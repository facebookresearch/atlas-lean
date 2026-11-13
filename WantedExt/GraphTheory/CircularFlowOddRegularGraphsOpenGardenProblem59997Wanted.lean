/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Circular flow numbers of (2t + 1)-graphs (Open Problem Garden 59997)

Open Problem Garden, Circular flow numbers of `r`-graphs (E. Steffen): a `(2t + 1)`-regular graph
`G` is a `(2t + 1)`-graph if `|∂_G(X)| ≥ 2t + 1` for every `X ⊆ V(G)` with `|X|` odd. Conjecture:
for every integer `t > 1`, every `(2t + 1)`-graph `G` has circular flow number `F_c(G) ≤ 2 + 2/t`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import MathlibExt.Combinatorics.SimpleGraph.EdgeIndexedMultigraph

@[expose] public section

namespace MathlibExt.GraphTheory.CircularFlowOddRegularGraphsOpenGardenProblem59997Wanted

/-!
Source: Open Problem Garden, Circular flow numbers of r-graphs (node 59997; E. Steffen),
http://www.openproblemgarden.org/op/circular_flow_numbers_of_r_graphs. UnsolvedMath record
UM-00003136 (`OPG-59997`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are finite, loopless and may have parallel edges, as in Steffen's and Mattiolo-Steffen's
papers (`r`-graphs are multigraphs); they are MathlibExt `EdgeIndexedMultigraph`s on finite vertex
and edge types. A nowhere-zero `r`-flow is the source's: an orientation (the head of each edge) and
real values `φ` with `1 ≤ |φ(e)| ≤ r - 1` and equal in- and out-sums at every vertex. `F_c(G)` is
the infimum of the `r` admitting one; the conjecture is read as: this set is nonempty and its
infimum is at most `2 + 2/t`. `∂_G(X)` is the set of edges with exactly one end in `X`.
-/

open SimpleGraph

/-- The number `|∂(X)|` of edges of the multigraph `M` with exactly one end in `X`. -/
noncomputable def cutSize {V E : Type} (M : EdgeIndexedMultigraph V E) (X : Set V) : ℕ :=
  {e | ∃ u ∈ M.ends e, ∃ w ∈ M.ends e, u ∈ X ∧ w ∉ X}.ncard

/-- `M` is an `r`-graph: `r`-regular, with `|∂(X)| ≥ r` for every vertex set `X` of odd size. -/
def IsRGraph {V E : Type} (M : EdgeIndexedMultigraph V E) (r : ℕ) : Prop :=
  (∀ v, M.degree v = r) ∧ ∀ X : Finset V, Odd X.card → r ≤ cutSize M X

open Classical in
/-- A nowhere-zero `r`-flow on `M`: an orientation, given by the head `head e ∈ ends e` of each
edge, and values `φ e` with `1 ≤ |φ e| ≤ r - 1` such that at every vertex the values on entering
edges and on leaving edges have the same sum. -/
def HasNowhereZeroFlow {V E : Type} [Fintype E] (M : EdgeIndexedMultigraph V E) (r : ℝ) : Prop :=
  ∃ (head : E → V) (φ : E → ℝ), (∀ e, head e ∈ M.ends e) ∧ (∀ e, 1 ≤ |φ e| ∧ |φ e| ≤ r - 1) ∧
    ∀ v, (∑ e, if head e = v then φ e else 0) =
      ∑ e, if v ∈ M.ends e ∧ head e ≠ v then φ e else 0

/-- Steffen's conjecture: for every integer `t > 1`, every `(2t + 1)`-graph `G` (finite, loopless,
parallel edges allowed) has circular flow number `F_c(G) = inf {r | G has a nowhere-zero r-flow}`
at most `2 + 2 / t`. -/
def circularFlowOddRegularGraphs : Prop :=
  ∀ (t : ℕ), 1 < t → ∀ (V E : Type) [Fintype V] [Fintype E] (M : EdgeIndexedMultigraph V E),
    IsRGraph M (2 * t + 1) →
      {r : ℝ | HasNowhereZeroFlow M r}.Nonempty ∧
        sInf {r : ℝ | HasNowhereZeroFlow M r} ≤ 2 + 2 / (t : ℝ)

/--
Resolved false: Mattiolo and Steffen construct, for every odd `p ≥ 3` and `t = 2p`, a `(2t +
1)`-regular class 1 graph (with parallel edges) of circular flow number greater than `2 + 2/t`;
class 1 regular graphs are `(2t + 1)`-graphs, and the paper states that this disproves the
conjecture for `(2t + 1)`-graphs. Source: Open Problem Garden, Circular flow numbers of r-graphs
(node 59997; E. Steffen), http://www.openproblemgarden.org/op/circular_flow_numbers_of_r_graphs;
resolution: D. Mattiolo and E. Steffen, Edge colorings and circular flows on regular graphs, J.
Graph Theory 99 (2022), 399-413, doi:10.1002/jgt.22746; arXiv:2001.02484, Section 1: Conjecture 1.5
([11], Steffen): 'Let G be a (2t+1)-graph. Then φ_c(G) ≤ 2 + 2/t'; 'Since (2t+1)-regular class 1
graphs are (2t+1)-graphs Conjecture 1.5 implies Conjecture 1.4. We show that both these conjectures
are false'; Corollary 3.5: for every odd p ≥ 3 and k = 2p there is a (2k+1)-regular class 1 graph G
with φ_c(G) > 2 + 2/k (graphs may have multiple edges), https://doi.org/10.1002/jgt.22746.
-/
public theorem_wanted circularFlowOddRegularGraphs_refuted : ¬ circularFlowOddRegularGraphs

end MathlibExt.GraphTheory.CircularFlowOddRegularGraphsOpenGardenProblem59997Wanted
