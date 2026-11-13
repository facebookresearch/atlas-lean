/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A long percolation cluster without a giant component on expanders (Benjamini, Open problem 11.7)

Benjamini, Coarse Geometry and Randomness, Open problem 11.7 (also Question 5.5 of Euclidean vs.
graph metric): let `G` be an expander and suppose some vertex `v` has, for percolation with `p =
1/2`, a cluster of diameter greater than `diam(G)/2` with probability greater than `1/2`. Show that
`1/2`-percolation on `G` contains a giant component with high probability.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import MathlibExt.Probability.ProductBondPercolation

@[expose] public section

namespace MathlibExt.Probability.LongClusterGiantComponentAMR99Problem0044Wanted

/-!
Source: I. Benjamini, Coarse Geometry and Randomness (Saint-Flour lecture notes 2011; Lecture Notes
in Mathematics 2100, Springer 2013), Open problem 11.7, PDF p. 86. UnsolvedMath record UM-10000044
(`AMR-099-0044`), dataset ulamai/UnsolvedMath v1.8.0.

'Expander' and 'with high probability' only make sense for sequences: the graphs are `(b,
d)`-expanders (maximum degree at most `d`, every set `S` of at most half of the vertices has at
least `b |S|` edges leaving it; the definition of Krivelevich-Lubetzky-Sudakov) with fixed `b > 0`,
`d`, and `|V(G_k)| → ∞`. Percolation is bond percolation (MathlibExt `gbernoulliLaw`, `gcluster`);
the diameter of the cluster is measured inside the cluster, and a giant component is a cluster with
at least `c |V(G_k)|` vertices for a fixed `c > 0`. The cluster-diameter hypothesis is written
`diam(G_k) < 2 diam(C_v)`.
-/

open Filter Topology MathlibExt.Probability.ProductBondPercolation

/-- A finite graph is a `(b, d)`-expander (Krivelevich-Lubetzky-Sudakov) when every vertex has
degree at most `d` and every set `S` of at most half of the vertices has at least `b |S|` edges
leaving it (the edges from `S` to its complement are counted once each, from their end in `S`). -/
def IsExpander {V : Type*} [Fintype V] [DecidableEq V] (b : ℝ) (d : ℕ) (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  (∀ x : V, G.degree x ≤ d) ∧
    ∀ S : Finset V, 2 * S.card ≤ Fintype.card V →
      b * S.card ≤ ∑ x ∈ S, ((G.neighborFinset x) \ S).card

/-- The diameter of the open cluster of `x` for the edge configuration `ω`, measured in the cluster
itself (the graph distance of the open subgraph restricted to the cluster). -/
noncomputable def clusterDiam {V : Type*} (G : SimpleGraph V) (ω : Sym2 V → Bool) (x : V) : ℕ :=
  ((openSubgraph G ω).induce (gcluster G ω x)).diam

/-- Benjamini's Open problem 11.7 (Coarse Geometry and Randomness; also Question 5.5 of Euclidean
vs. graph metric), for sequences of graphs: if `G_k` are `(b, d)`-expanders whose numbers of
vertices tend to infinity, with vertices `v_k` such that in bond percolation with `p = 1/2` the
cluster of `v_k` has diameter greater than `diam(G_k)/2` with probability greater than `1/2`, then
`1/2`-percolation on `G_k` has a giant component with high probability: there is `c > 0` such
that the probability that some cluster has at least `c |V(G_k)|` vertices tends to `1`. -/
def longClusterGivesGiant : Prop :=
  ∀ (b : ℝ) (d : ℕ), 0 < b →
    ∀ (V : ℕ → Type) [∀ k, Fintype (V k)] [∀ k, DecidableEq (V k)]
      (G : ∀ k, SimpleGraph (V k)) [∀ k, DecidableRel (G k).Adj] (v : ∀ k, V k),
      Tendsto (fun k => Fintype.card (V k)) atTop atTop →
      (∀ k, IsExpander b d (G k)) →
      (∀ k, (1 / 2 : ENNReal) < gbernoulliLaw (1 / 2) (by norm_num) (by norm_num)
        {ω : Sym2 (V k) → Bool | (G k).diam < 2 * clusterDiam (G k) ω (v k)}) →
      ∃ c : ℝ, 0 < c ∧
        Tendsto (fun k => gbernoulliLaw (1 / 2) (by norm_num) (by norm_num)
          {ω : Sym2 (V k) → Bool | ∃ x : V k, c * Fintype.card (V k) ≤ (gcluster (G k) ω x).ncard})
          atTop (𝓝 1)

/--
Resolved false: Krivelevich-Lubetzky-Sudakov construct `(b, d)`-expanders on `n` vertices, for
infinitely many `n`, in which the cluster of a prescribed vertex has diameter at least `(1 - ε)
diam(G)` with probability at least `1 - ε`, while with high probability no cluster has more than
`n^{1-δ}` vertices; with `p = 1/2` and `ε = 1/4` these graphs satisfy the hypothesis and have no
giant component. Source: I. Benjamini, Coarse Geometry and Randomness (Saint-Flour lecture notes
2011; Lecture Notes in Mathematics 2100, Springer 2013), Open problem 11.7, PDF p. 86; resolution:
M. Krivelevich, E. Lubetzky and B. Sudakov, Asymptotics in percolation on high-girth expanders,
Random Structures Algorithms 56 (2020), 927-947; arXiv:1803.11553, abstract: the construction
'answer[s] negatively a question of Benjamini (2013) on the relation between the diameter of a
component in percolation on expanders and the existence of a giant component'; Section 1, Question
(Benjamini [3, Q. 5.5]) and Theorem 3: for every ε > 0 and 0 < p < 1 there are b, d, δ > 0 and, for
infinitely many n, a (b, d)-expander G on n vertices with a vertex v such that P(diam(Cv(G)) ≥ (1 -
ε) diam(G)) ≥ 1 - ε while w.h.p. no component has more than n^{1-δ} vertices (apply it with p = 1/2
and ε = 1/4), https://arxiv.org/abs/1803.11553.
-/
public theorem_wanted longClusterGivesGiant_refuted : ¬ longClusterGivesGiant

end MathlibExt.Probability.LongClusterGiantComponentAMR99Problem0044Wanted
