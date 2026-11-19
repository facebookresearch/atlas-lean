/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Spanning hypercubes in random graphs (Erdős Problem 578)

Erdős Problem 578 (Erdős and Bollobás): if `G` is a random graph on `2^d` vertices, including each
edge with probability `1/2`, then `G` almost surely contains a copy of `Q_d`, the `d`-dimensional
hypercube.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import MathlibExt.Combinatorics.SimpleGraph.HypercubeExtremal

@[expose] public section

namespace MathlibExt.GraphTheory.RandomGraphSpanningHypercubeErdosProblem578Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #578, https://www.erdosproblems.com/578 (status
PROVED). UnsolvedMath record UM-30006937 (`EP-578`), dataset ulamai/UnsolvedMath v1.8.0.

With edge probability `1/2` all labelled graphs on `Fin (2^d)` are equally likely, so the
probability is the proportion of those graphs that contain `Q_d` as a subgraph, not necessarily
induced (`SimpleGraph.IsContained`); almost surely means that this tends to `1` as `d → ∞`. `Q_d` is
MathlibExt's `SimpleGraph.hypercubeGraph d`, the graph on `Fin d → Bool` joining vectors that differ
in exactly one coordinate. Compared with the
formal-conjectures statement `ErdosProblems/578.lean` (equivalent, with counting in place of
formal-conjectures' `binomialRandom`; no code imported).
-/

open Classical in
/-- The probability that the random graph `G(2^d, 1/2)` contains a copy of `Q_d`: the proportion
of the graphs on the vertex set `Fin (2 ^ d)` that contain `Q_d` as a (not necessarily induced)
subgraph. -/
noncomputable def hypercubeContainmentProbability (d : ℕ) : ℝ :=
  ((Finset.univ.filter fun G : SimpleGraph (Fin (2 ^ d)) =>
      (SimpleGraph.hypercubeGraph d).IsContained G).card : ℝ) /
    Fintype.card (SimpleGraph (Fin (2 ^ d)))

/-- Erdős Problem 578 (Erdős and Bollobás): the random graph `G(2^d, 1/2)` contains a copy of
`Q_d` with probability tending to `1` as `d → ∞`. -/
def randomGraphContainsHypercube : Prop :=
  Filter.Tendsto hypercubeContainmentProbability Filter.atTop (nhds 1)

/--
Resolved true: Riordan proved that `G(2^d, p)` contains a copy of `Q_d` with probability tending to
`1` for every fixed edge probability `p > 1/4`, in particular for `p = 1/2`; erdosproblems.com/578
lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #578,
https://www.erdosproblems.com/578 (status PROVED); resolution: O. Riordan, Spanning subgraphs of
random graphs, Combin. Probab. Comput. (2000), 125-148, erdosproblems.com/578: solved by Riordan,
who proved this for any edge probability greater than 1/4,
https://doi.org/10.1017/S0963548399004150.
-/
public theorem_wanted randomGraphContainsHypercube_holds : randomGraphContainsHypercube

end MathlibExt.GraphTheory.RandomGraphSpanningHypercubeErdosProblem578Wanted
