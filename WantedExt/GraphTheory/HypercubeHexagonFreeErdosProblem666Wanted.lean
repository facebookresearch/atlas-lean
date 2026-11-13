/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hexagon-free subgraphs of the hypercube (Erdős Problem 666)

Erdős Problem 666: let `Q_n` be the `n`-dimensional hypercube graph (`2^n` vertices, `n 2^{n-1}`
edges). Is it true that, for every `ε > 0`, if `n` is sufficiently large, every subgraph of `Q_n`
with `≥ ε n 2^{n-1}` many edges contains a `C₆`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Order.Filter.AtTopBot.Defs
public import MathlibExt.Combinatorics.SimpleGraph.HypercubeExtremal

@[expose] public section

namespace MathlibExt.GraphTheory.HypercubeHexagonFreeErdosProblem666Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #666, https://www.erdosproblems.com/666 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006975 (`EP-666`), dataset ulamai/UnsolvedMath v1.8.0.

`Q_n` is MathlibExt's `SimpleGraph.hypercubeGraph n` on `Fin n → Bool` (adjacent iff the vertices
differ in exactly one coordinate). A subgraph is `H ≤ Q_n` (spanning; isolated vertices do not
matter); "contains a `C₆`" is `cycleGraph 6 ⊑ H`. Compared with the formal-conjectures statement
`ErdosProblems/666.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 666: for every `ε > 0` and every sufficiently large `n`, every subgraph of the
hypercube `Q_n` with at least `ε n 2^(n-1)` edges contains a `6`-cycle `C₆`. -/
def denseHypercubeSubgraphContainsHexagon : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, ∀ H : SimpleGraph (Fin n → Bool),
    H ≤ SimpleGraph.hypercubeGraph n → ε * n * 2 ^ (n - 1) ≤ (H.edgeSet.ncard : ℝ) →
      (SimpleGraph.cycleGraph 6).IsContained H

/--
Resolved false: Chung and Brouwer, Dejter and Thomassen partitioned the edges of `Q_n` into four
subgraphs containing no `C₆`, so one of them has at least `n 2^{n-1} / 4` edges and no `C₆`, and the
claim fails for `ε = 1/4`; erdosproblems.com/666 lists the problem as disproved. Source: T. F.
Bloom, Erdős Problems, Problem #666, https://www.erdosproblems.com/666 (status DISPROVED (LEAN));
resolution: F. R. K. Chung, Subgraphs of a hypercube containing no small even cycles, J. Graph
Theory 16 (1992), 273-286; A. E. Brouwer, I. J. Dejter and C. Thomassen, Highly symmetric subgraphs
of hypercubes, J. Algebraic Combin. 2 (1993), 25-29, erdosproblems.com/666: the answer is no; Chung
and Brouwer-Dejter-Thomassen constructed an edge-partition of Q_n into four subgraphs, each
containing no C₆, https://www.erdosproblems.com/666.
-/
public theorem_wanted denseHypercubeSubgraphContainsHexagon_refuted :
    ¬ denseHypercubeSubgraphContainsHexagon

end MathlibExt.GraphTheory.HypercubeHexagonFreeErdosProblem666Wanted
