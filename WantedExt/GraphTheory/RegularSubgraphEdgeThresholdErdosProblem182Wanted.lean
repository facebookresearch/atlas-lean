/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Graphs without `k`-regular subgraphs (Erdős Problem 182)

Erdős Problem 182 (Erdős and Sauer): let `k ≥ 3`. What is the maximum number of edges of a graph on
`n` vertices with no `k`-regular subgraph? Is it `≪ n^{1 + o(1)}`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Subgraph

@[expose] public section

namespace MathlibExt.GraphTheory.RegularSubgraphEdgeThresholdErdosProblem182Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #182, https://www.erdosproblems.com/182 (status
PROVED). UnsolvedMath record UM-30006753 (`EP-182`), dataset ulamai/UnsolvedMath v1.8.0.

A `k`-regular subgraph is a subgraph with at least one vertex in which every vertex has exactly `k`
neighbours; without nonemptiness the empty subgraph would qualify. `≪ n^{1 + o(1)}` is stated as:
for every `ε > 0` and all large `n`, at least `n^{1 + ε}` edges force a `k`-regular subgraph. The
exact order `n log log n` (Janzer and Sudakov, matching Pyber, Rödl and Szemerédi) is not
formalized.
-/

open Filter

/-- `G` has a nonempty `k`-regular subgraph: a subgraph with at least one vertex in which every
vertex has exactly `k` neighbours. -/
def HasRegularSubgraph {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ H : G.Subgraph, H.verts.Nonempty ∧ ∀ v ∈ H.verts, (H.neighborSet v).ncard = k

/-- Erdős Problem 182: for every `k ≥ 3`, an `n`-vertex graph with no `k`-regular subgraph has at
most `n^{1 + o(1)}` edges: for every `ε > 0` and all large `n`, every graph on `n` vertices with at
least `n^{1 + ε}` edges has a `k`-regular subgraph. -/
def regularSubgraphThresholdAlmostLinear : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
    (n : ℝ) ^ (1 + ε) ≤ G.edgeSet.ncard → HasRegularSubgraph G k

/--
Resolved true: Janzer and Sudakov prove that every `n`-vertex graph with average degree at least
`C_k log log n` contains a `k`-regular subgraph; `n^{1 + ε}` edges give average degree `2 n^ε`,
which exceeds `C_k log log n` for large `n`. erdosproblems.com/182 lists the problem as proved.
Source: T. F. Bloom, Erdős Problems, Problem #182, https://www.erdosproblems.com/182 (status
PROVED); resolution: O. Janzer and B. Sudakov, Resolution of the Erdős-Sauer problem on regular
subgraphs, Forum Math. Pi 11 (2023), e19, arXiv:2204.12455, main theorem: every n-vertex graph with
average degree at least C_k log log n contains a k-regular subgraph,
https://doi.org/10.1017/fmp.2023.19.
-/
public theorem_wanted regularSubgraphThresholdAlmostLinear_holds :
    regularSubgraphThresholdAlmostLinear

end MathlibExt.GraphTheory.RegularSubgraphEdgeThresholdErdosProblem182Wanted
