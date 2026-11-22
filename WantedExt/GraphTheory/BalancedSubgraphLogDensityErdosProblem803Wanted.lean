/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Balanced subgraphs of graphs with `n log n` edges (Erdős Problem 803)

Erdős Problem 803 (Erdős and Simonovits): call `H` `D`-balanced if its maximum degree is at most `D`
times its minimum degree. Is it true that for every `m ≥ 1`, if `n` is sufficiently large, any graph
on `n` vertices with at least `n log n` edges contains an `O(1)`-balanced subgraph with `m` vertices
and `≫ m log m` edges (the implied constants absolute)?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import MathlibExt.Combinatorics.SimpleGraph.Balanced

@[expose] public section

namespace MathlibExt.GraphTheory.BalancedSubgraphLogDensityErdosProblem803Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #803, https://www.erdosproblems.com/803 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30007041 (`EP-803`), dataset ulamai/UnsolvedMath v1.8.0.

`D`-balanced is `MathlibExt`'s `SimpleGraph.IsBalanced` applied to the subgraph as a graph on its
vertex set; subgraphs need not be induced. The constants `D` and `c` come before `m`, as 'absolute'
requires. Compared with the formal-conjectures statement `ErdosProblems/803.lean` (equivalent; no
code imported).
-/

open Classical in
/-- Erdős Problem 803 (Erdős and Simonovits): there are absolute constants `D` and `c > 0` such that
for every `m ≥ 1` and all large `n`, every graph on `n` vertices with at least `n log n` edges has a
`D`-balanced subgraph on `m` vertices with at least `c m log m` edges. -/
def balancedDenseSubgraphs : Prop :=
  ∃ D c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m → ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph (Fin n),
    (n : ℝ) * Real.log n ≤ G.edgeSet.ncard →
      ∃ H : G.Subgraph, H.verts.ncard = m ∧ H.coe.IsBalanced D ∧
        c * m * Real.log m ≤ H.edgeSet.ncard

/--
Resolved false: Alon showed that for every `D > 1` and all large `n` some graph with `n` vertices
(isolated vertices added to his construction) and at least `n log n` edges has only `D`-balanced
subgraphs `H` on `m` vertices with `e(H) = O_D(m √(log m))` edges (Proposition 2.1: the average
degree of `H` is below `36(4 √(log₂ m) + log₂(64D) + 18)`), which is below `c m log m` for large
`m`; erdosproblems.com/803 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems,
Problem #803, https://www.erdosproblems.com/803 (status DISPROVED (LEAN)); resolution: N. Alon,
Problems and results in extremal combinatorics. II, Discrete Math. 308 (2008), 4460-4472, Section 2,
Proposition 2.1: for every D > 1 and n > 10^5 there is a graph with at most 2n vertices and at least
2n log₂(2n) edges in which every subgraph with m vertices, average degree at least d and maximum
degree at most Dd has d < 36(4 √(log₂ m) + log₂(64D) + 18), answering the Erdős-Simonovits question
in the negative ('In this section we show that this is not true'),
https://web.math.princeton.edu/~nalon/PDFS/extremalII1.pdf.
-/
public theorem_wanted balancedDenseSubgraphs_refuted : ¬ balancedDenseSubgraphs

end MathlibExt.GraphTheory.BalancedSubgraphLogDensityErdosProblem803Wanted
