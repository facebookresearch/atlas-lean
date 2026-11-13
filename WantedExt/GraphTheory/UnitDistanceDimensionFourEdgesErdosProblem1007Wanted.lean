/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fewest edges of a graph of dimension four (Erdős Problem 1007)

Erdős Problem 1007: the dimension of a graph `G` is the least `n` such that `G` embeds in `ℝⁿ` with
every edge a unit segment. What is the smallest number of edges in a graph of dimension `4`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace MathlibExt.GraphTheory.UnitDistanceDimensionFourEdgesErdosProblem1007Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1007, https://www.erdosproblems.com/1007 (status
SOLVED (LEAN)). UnsolvedMath record UM-30007121 (`EP-1007`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are finite (vertex type `Fin n`). An embedding is an injective map into `EuclideanSpace ℝ
(Fin n)` with edges of length `1`; distances between non-adjacent vertices are unconstrained, as in
Erdős, Harary and Tutte. Every finite graph has such an embedding (all pairwise distances `1` in
dimension `|V|`), so the infimum is attained. The answer is stated as `IsLeast` of the edge counts
of dimension-`4` graphs. Compared with the formal-conjectures statement `ErdosProblems/1007.lean`
(equivalent; no code imported).
-/

/-- `G` has a unit-distance embedding in `ℝⁿ`: an injective map of its vertices into
`EuclideanSpace ℝ (Fin n)` under which every edge has length `1` (non-edges are unconstrained). -/
def HasUnitEmbedding {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧
    ∀ u v, G.Adj u v → dist (f u) (f v) = 1

/-- The dimension of a finite graph: the least `n` such that it has a unit-distance embedding in
`ℝⁿ`. -/
noncomputable def graphDimension {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {n | HasUnitEmbedding G n}

/-- Erdős Problem 1007: the least number of edges of a finite graph of dimension `4` is `9`. -/
def minEdgesDimensionFourEqNine : Prop :=
  IsLeast {m : ℕ | ∃ (n : ℕ) (G : SimpleGraph (Fin n)), graphDimension G = 4 ∧
    G.edgeSet.ncard = m} 9

/--
Resolved true: House proved that a graph of dimension `4` has at least `9` edges, and `K_{3,3}` has
dimension `4` and `9` edges (Chaffee and Noble give another proof); erdosproblems.com/1007 lists the
problem as solved, with a formal proof in plby/lean-proofs (`Erdos1007.lean`). Source: T. F. Bloom,
Erdős Problems, Problem #1007, https://www.erdosproblems.com/1007 (status SOLVED (LEAN));
resolution: R. F. House, A 4-dimensional graph has at least 9 edges, Discrete Math. (2013),
1783-1789; J. Chaffee and M. Noble, Dimension 4 and dimension 5 graphs with minimum edge set,
Australas. J. Combin. (2016), 327-333; formal proof plby/lean-proofs,
src/v4.29.1/ErdosProblems/Erdos1007.lean, the minimum is 9, attained only by K_{3,3}
(erdosproblems.com/1007),
https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1007.lean.
-/
public theorem_wanted minEdgesDimensionFourEqNine_holds : minEdgesDimensionFourEqNine

end MathlibExt.GraphTheory.UnitDistanceDimensionFourEdgesErdosProblem1007Wanted
