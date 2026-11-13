/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bipartition number of random graphs (Erdős Problem 807)

Erdős Problem 807: is `τ(G) = n - α(G)` almost surely for the random graph `G(n, 1/2)`, where `τ(G)`
is the least number of pairwise edge-disjoint complete bipartite graphs whose union is `G` and
`α(G)` is the independence number?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.GraphTheory.RandomGraphBipartitionNumberErdosProblem807Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #807, https://www.erdosproblems.com/807 (status
DISPROVED). UnsolvedMath record UM-30007044 (`EP-807`), dataset ulamai/UnsolvedMath v1.8.0.

`G(n, 1/2)` is the uniform distribution on the graphs on `Fin n`; "almost surely" is the proportion
of graphs with the property tending to `1`. Complete bipartite subgraphs have nonempty sides; the
empty graph has `τ = 0`.
-/

/-- `H` is a complete bipartite graph with nonempty sides `L` and `R`: its edges are exactly the
pairs with one end in each side (vertices outside `L ∪ R` are isolated). -/
def IsCompleteBipartite {V : Type*} (H : SimpleGraph V) : Prop :=
  ∃ L R : Set V, Disjoint L R ∧ L.Nonempty ∧ R.Nonempty ∧
    ∀ u v, H.Adj u v ↔ (u ∈ L ∧ v ∈ R) ∨ (u ∈ R ∧ v ∈ L)

/-- The bipartition number `τ(G)`: the least number of pairwise edge-disjoint complete bipartite
subgraphs of `G` whose union is `G`. -/
noncomputable def bipartitionNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ B : Fin k → SimpleGraph V, (∀ i, B i ≤ G ∧ IsCompleteBipartite (B i)) ∧
    (∀ i j, i ≠ j → Disjoint (B i).edgeSet (B j).edgeSet) ∧ G.edgeSet = ⋃ i, (B i).edgeSet}

open Classical in
/-- The proportion of the graphs on `Fin n` (the uniform model `G(n, 1/2)`) with
`τ(G) = n - α(G)`. -/
noncomputable def bipartitionEqualityProportion (n : ℕ) : ℝ :=
  ((Finset.univ.filter fun G : SimpleGraph (Fin n) => bipartitionNumber G = n - G.indepNum).card :
      ℝ) / Fintype.card (SimpleGraph (Fin n))

/-- Erdős Problem 807: almost surely `τ(G) = n - α(G)` for the random graph `G(n, 1/2)`, that is,
the proportion of graphs on `n` vertices with `τ(G) = n - α(G)` tends to `1`. -/
def bipartitionNumberAlmostSurelyEq : Prop :=
  Filter.Tendsto bipartitionEqualityProportion Filter.atTop (nhds 1)

/--
Resolved false: Alon showed that for `n` in a set of density 1 the random graph `G(n, 1/2)` has
`τ(G) ≤ n - α(G) - 1` with high probability, so the proportion with equality tends to `0` along
those `n`; Alon, Bohman and Huang (Theorem 1.1) improved this to `τ(G) ≤ n - (1 + c) α(G)`.
erdosproblems.com/807 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem
#807, https://www.erdosproblems.com/807 (status DISPROVED); resolution: N. Alon, Bipartite
decomposition of random graphs, J. Combin. Theory Ser. B 113 (2015), 220-235; N. Alon, T. Bohman and
H. Huang, More on the bipartite decomposition of random graphs, J. Graph Theory 84 (2017), 45-52,
arXiv:1409.6165, Alon: for n in a set of density 1, τ(G) ≤ n - α(G) - 1 whp; Alon-Bohman-Huang
Theorem 1.1: τ(G) ≤ n - (1 + c) α(G) whp, https://arxiv.org/abs/1409.6165.
-/
public theorem_wanted bipartitionNumberAlmostSurelyEq_refuted : ¬ bipartitionNumberAlmostSurelyEq

end MathlibExt.GraphTheory.RandomGraphBipartitionNumberErdosProblem807Wanted
