/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Induced subgraphs of Ramsey graphs with distinct sizes (Erdős Problem 636)

Erdős Problem 636 (Erdős, Faudree and Sós): suppose `G` is a graph on `n` vertices which contains no
complete graph or independent set on `≫ log n` many vertices. Must `G` contain `≫ n^{5/2}` induced
subgraphs which pairwise differ in either the number of vertices or the number of edges?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.RamseyGraphDistinctInducedSizesErdosProblem636Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #636, https://www.erdosproblems.com/636 (status
PROVED). UnsolvedMath record UM-30006961 (`EP-636`), dataset ulamai/UnsolvedMath v1.8.0.

The hypothesis 'no complete graph or independent set on `≫ log n` vertices' is `ω(G) < C log n` and
`α(G) < C log n` for a constant `C > 0` (natural logarithm); the conclusion's constant may depend on
`C`, and the statement is for all large `n`, as in the resolving paper. A largest family of induced
subgraphs pairwise differing in vertex or edge count has one member for each value of `(|U|,
e(G[U]))`, so its size is the number of those pairs. Compared with the formal-conjectures statement
`ErdosProblems/636.lean` (equivalent; no code imported).
-/

open Classical in
/-- The number of distinct pairs `(|U|, e(G[U]))` over the vertex sets `U` of `G`: the largest
number of induced subgraphs of `G` that pairwise differ in their number of vertices or their number
of edges. -/
noncomputable def distinctInducedSizes {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).image fun U =>
    (U.card, (G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ U).card)).card

/-- Erdős Problem 636 (Erdős, Faudree and Sós): for every `C > 0` there is `c > 0` such that for
large `n` every graph on `n` vertices with no clique and no independent set of `C log n` vertices
has at least `c n^{5/2}` induced subgraphs pairwise differing in their number of vertices or of
edges. -/
def ramseyGraphManyInducedSizes : Prop :=
  ∀ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph (Fin n),
    (G.cliqueNum : ℝ) < C * Real.log n → (G.indepNum : ℝ) < C * Real.log n →
      c * (n : ℝ) ^ (5 / 2 : ℝ) ≤ distinctInducedSizes G

/--
Resolved true: Kwan and Sudakov proved the conjecture of Erdős, Faudree and Sós: an `n`-vertex graph
with no clique or independent set of size `C log n` has `Ω_C(n^{5/2})` induced subgraphs, no two
with the same numbers of vertices and edges; erdosproblems.com/636 lists the problem as proved.
Source: T. F. Bloom, Erdős Problems, Problem #636, https://www.erdosproblems.com/636 (status
PROVED); resolution: M. Kwan and B. Sudakov, Proof of a conjecture on induced subgraphs of Ramsey
graphs, Trans. Amer. Math. Soc. (2019), 5571-5594, arXiv:1712.05656, abstract: in any C-Ramsey graph
(no clique or independent set of size C log n) there are Ω(n^{5/2}) induced subgraphs, no pair of
which have the same numbers of vertices and edges, https://arxiv.org/abs/1712.05656.
-/
public theorem_wanted ramseyGraphManyInducedSizes_holds : ramseyGraphManyInducedSizes

end MathlibExt.GraphTheory.RamseyGraphDistinctInducedSizesErdosProblem636Wanted
