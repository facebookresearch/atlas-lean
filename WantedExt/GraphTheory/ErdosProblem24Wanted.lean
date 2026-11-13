/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 24
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

@[expose] public section

namespace MathlibExt.GraphTheory.ErdosProblem24Wanted

/-! Source record `FC-ErdosProblem24`, ported from FormalConjectures
`ErdosProblems/24.lean` (`theorem erdos_24`) and checked against
erdosproblems.com/24. `CliqueFree`, `copyCount`, and `cycleGraph` are
Mathlib's. The `answer(True)` wrapper is elaborated to the direct claim.
Status: resolved true for `C₅` (Grzesik;
Hatami–Hladký–Králʼ–Norine–Razborov). The broader fixed odd-cycle family
asked for in the source is not formalized here. -/

/-- **Pentagons in triangle-free graphs (Erdős Problem 24).** For every natural number $n$, every
graph on $5n$ vertices with no three pairwise adjacent vertices has at most $n^5$ subgraphs
isomorphic to the $5$-cycle $C_5$. -/
def conjecture : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (5 * n))), G.CliqueFree 3 →
    G.copyCount (SimpleGraph.cycleGraph 5) ≤ n ^ 5

/-- **Pentagon bound for triangle-free graphs (five-cycle case of Erdős Problem 24).** For every
natural number $n$, every graph on $5n$ vertices with no three pairwise adjacent vertices has at
most $n^5$ subgraphs isomorphic to the $5$-cycle $C_5$.

Source: Erdős Problems, Problem 24 (records the Grzesik and
Hatami–Hladký–Králʼ–Norine–Razborov resolution), https://www.erdosproblems.com/24; Andrzej
Grzesik, On the maximum number of five-cycles in a triangle-free graph, arXiv:1102.0962v3,
https://arxiv.org/abs/1102.0962v3; Hamed Hatami, Jan Hladky, Daniel Kral, Serguei Norine, and
Alexander Razborov, On the number of pentagons in triangle-free graphs, arXiv:1102.1634v4,
https://arxiv.org/abs/1102.1634v4. Moved from `OpenConjectures/GraphTheory/ErdosProblem24`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.GraphTheory.ErdosProblem24Wanted
