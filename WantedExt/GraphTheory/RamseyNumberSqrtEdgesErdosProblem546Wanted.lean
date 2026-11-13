/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ramsey numbers of graphs with `m` edges (Erdős Problem 546)

Erdős Problem 546: let `G` be a graph with no isolated vertices and `m` edges. Is it true that `R(G)
≤ 2^{O(m^{1/2})}`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Combinatorics.SimpleGraph.Ramsey

@[expose] public section

namespace MathlibExt.GraphTheory.RamseyNumberSqrtEdgesErdosProblem546Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #546, https://www.erdosproblems.com/546 (status
PROVED). UnsolvedMath record UM-30006926 (`EP-546`), dataset ulamai/UnsolvedMath v1.8.0.

`R(G)` is the two-colour Ramsey number, MathlibExt's `SimpleGraph.diagonalGraphRamsey`: the least
`N` such that for every graph `R` on `Fin N` (the red edges; the blue edges form the complement
`Rᶜ`) the graph `G` is a subgraph, not necessarily induced, of `R` or of `Rᶜ`. Graphs are finite (`V
: Type` with `Fintype V`); no isolated vertices is `∀ v, ∃ w, G.Adj v w`; `2^{O(√m)}` is `∃ C, R(G)
≤ 2^{C √m}` for all such `G`. Compared with the formal-conjectures statement
`ErdosProblems/546.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 546: there is a constant `C` such that every finite graph `G` with no isolated
vertices and `m` edges has `R(G) ≤ 2 ^ (C √m)`. -/
def ramseyNumberSqrtEdgeBound : Prop :=
  ∃ C : ℝ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), (∀ v, ∃ w, G.Adj v w) →
    (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ (2 : ℝ) ^ (C * Real.sqrt G.edgeSet.ncard)

/--
Resolved true: Sudakov proved Erdős' conjecture that there is an absolute constant `c` with `R(G) ≤
2^{c √m}` for every graph `G` with `m` edges and no isolated vertices; erdosproblems.com/546 lists
the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #546,
https://www.erdosproblems.com/546 (status PROVED); resolution: B. Sudakov, A conjecture of Erdős on
graph Ramsey numbers, Adv. Math. (2011), 601-609, abstract of arXiv:1002.0095: r(G) ≤ 2^{c√m} for
every graph G with m edges and no isolated vertices; erdosproblems.com/546: proved by Sudakov,
https://arxiv.org/abs/1002.0095.
-/
public theorem_wanted ramseyNumberSqrtEdgeBound_holds : ramseyNumberSqrtEdgeBound

end MathlibExt.GraphTheory.RamseyNumberSqrtEdgesErdosProblem546Wanted
