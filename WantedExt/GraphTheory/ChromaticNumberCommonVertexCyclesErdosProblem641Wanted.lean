/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Edge-disjoint cycles on a common vertex set (Erdős Problem 641)

Erdős Problem 641 (Erdős and Hajnal): is there some function `f` such that for all `k ≥ 1`, if a
finite graph `G` has chromatic number at least `f(k)` then `G` has `k` edge-disjoint cycles on the
same set of vertices?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

namespace MathlibExt.GraphTheory.ChromaticNumberCommonVertexCyclesErdosProblem641Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #641, https://www.erdosproblems.com/641 (status
DISPROVED). UnsolvedMath record UM-30006964 (`EP-641`), dataset ulamai/UnsolvedMath v1.8.0.

Cycles are closed walks with `Walk.IsCycle`; `k` cycles are on the same vertex set when their
supports coincide, and edge-disjoint when no edge lies on two of them. Graphs are on `Fin n`;
`chromaticNumber` is Mathlib's (in `ℕ∞`). Compared with the formal-conjectures statement
`ErdosProblems/641.lean` (equivalent; formal-conjectures encodes the cycles as an embedded union of
connected `2`-regular graphs; no code imported).
-/

/-- `G` has `k` pairwise edge-disjoint cycles all with the same vertex set `S`. -/
def HasEdgeDisjointCyclesOnCommonVertices {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (S : Set V) (v : Fin k → V) (w : ∀ i, G.Walk (v i) (v i)),
    (∀ i, (w i).IsCycle ∧ {x | x ∈ (w i).support} = S) ∧
      ∀ i j, i ≠ j → ∀ e ∈ (w i).edges, e ∉ (w j).edges

/-- Erdős Problem 641 (Erdős and Hajnal): there is `f` such that for every `k ≥ 1` every finite
graph with chromatic number at least `f(k)` has `k` edge-disjoint cycles on the same vertex
set. -/
def chromaticForcesCommonVertexCycles : Prop :=
  ∃ f : ℕ → ℕ, ∀ k : ℕ, 1 ≤ k → ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (f k : ℕ∞) ≤ G.chromaticNumber → HasEdgeDisjointCyclesOnCommonVertices G k

/--
Resolved false: Janzer, Steiner and Sudakov constructed `n`-vertex graphs with (fractional)
chromatic number `Ω(log log n / log log log n)` and no `4`-regular subgraph; two edge-disjoint
cycles on the same vertex set form a `4`-regular subgraph, so the claim fails already for `k = 2`.
erdosproblems.com/641 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem
#641, https://www.erdosproblems.com/641 (status DISPROVED); resolution: B. Janzer, R. Steiner and B.
Sudakov, Chromatic number and regular subgraphs, arXiv:2410.02437 (2024), abstract: there are
n-vertex graphs with fractional chromatic number Ω(log log n / log log log n) and no 4-regular
subgraph, so no such F(r) exists for r ≥ 2, https://arxiv.org/abs/2410.02437.
-/
public theorem_wanted chromaticForcesCommonVertexCycles_refuted :
    ¬ chromaticForcesCommonVertexCycles

end MathlibExt.GraphTheory.ChromaticNumberCommonVertexCyclesErdosProblem641Wanted
