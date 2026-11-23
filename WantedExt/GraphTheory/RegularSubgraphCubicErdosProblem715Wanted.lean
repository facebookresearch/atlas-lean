/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cubic subgraphs of regular graphs (Erdős Problem 715)

Erdős Problem 715 (Berge): does every regular graph of degree `4` contain a regular subgraph of
degree `3`? Is there any `r` such that every regular graph of degree `r` must contain a regular
subgraph of degree `3`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Subgraph

@[expose] public section

namespace MathlibExt.GraphTheory.RegularSubgraphCubicErdosProblem715Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #715, https://www.erdosproblems.com/715 (status
PROVED). UnsolvedMath record UM-30006988 (`EP-715`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are finite with a nonempty vertex set (the empty graph is vacuously `4`-regular). A
`3`-regular subgraph is a subgraph `H` with nonempty vertex set in which every vertex has exactly
`3` neighbours in `H` (not necessarily spanning or induced). Degrees are `Set.ncard` of neighbour
sets. The second question (is there any `r` such that every `r`-regular graph contains a `3`-regular
subgraph) is stated in the universal form the problem page records: every `r ≥ 4` works (Tashkinov
for `r = 4`, Alon-Friedland-Kalai for `r ≥ 5`); `r = 3` is trivial.
-/

/-- Erdős Problem 715, first question: every (finite, nonempty) `4`-regular graph contains a
`3`-regular subgraph, i.e. a subgraph with a nonempty vertex set in which every vertex has exactly
`3` neighbours. -/
def fourRegularContainsCubicSubgraph : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V), (∀ v, (G.neighborSet v).ncard = 4) →
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ ∀ v ∈ H.verts, (H.neighborSet v).ncard = 3

/-- Erdős Problem 715, second question, in the universal form the problem page records: for every
`r ≥ 4`, every finite nonempty `r`-regular graph contains a `3`-regular subgraph (for `r = 3` the
graph itself is one). -/
def regularDegreeAtLeastFourContainsCubicSubgraph : Prop :=
  ∀ r : ℕ, 4 ≤ r → ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
    (∀ v, (G.neighborSet v).ncard = r) →
      ∃ H : G.Subgraph, H.verts.Nonempty ∧ ∀ v ∈ H.verts, (H.neighborSet v).ncard = 3

/--
Resolved true: Tashkinov proved that every `4`-regular graph contains a `3`-regular subgraph;
erdosproblems.com/715 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#715, https://www.erdosproblems.com/715 (status PROVED); resolution: V. A. Tashkinov, Regular
subgraphs of regular graphs, Soviet Math. Dokl. 26 (1982), 37-38; N. Alon, S. Friedland and G.
Kalai, Every 4-regular graph plus an edge contains a 3-regular subgraph, J. Combin. Theory Ser. B 36
(1984), 92-93, erdosproblems.com/715: 'The answer is yes, proved by Tashkinov'; Alon, Friedland and
Kalai showed that every r-regular graph with r ≥ 5 contains a 3-regular subgraph,
https://www.erdosproblems.com/715.
-/
public theorem_wanted fourRegularContainsCubicSubgraph_holds : fourRegularContainsCubicSubgraph

/--
Resolved true: for `r = 4` this is Tashkinov's theorem, and Alon, Friedland and Kalai proved that
every `4`-regular graph plus an edge contains a `3`-regular subgraph, hence every `r`-regular graph
with `r ≥ 5` contains one (erdosproblems.com/715); so every `r ≥ 4` answers the second question.
Source: T. F. Bloom, Erdős Problems, Problem #715, https://www.erdosproblems.com/715 (status
PROVED); resolution: V. A. Tashkinov, Regular subgraphs of regular graphs, Soviet Math. Dokl. 26
(1982), 37-38; N. Alon, S. Friedland and G. Kalai, Every 4-regular graph plus an edge contains a
3-regular subgraph, J. Combin. Theory Ser. B 36 (1984), 92-93, erdosproblems.com/715: 'The answer is
yes, proved by Tashkinov'; Alon, Friedland and Kalai showed that every r-regular graph with r ≥ 5
contains a 3-regular subgraph, https://www.erdosproblems.com/715.
-/
public theorem_wanted regularDegreeAtLeastFourContainsCubicSubgraph_holds :
    regularDegreeAtLeastFourContainsCubicSubgraph

end MathlibExt.GraphTheory.RegularSubgraphCubicErdosProblem715Wanted
