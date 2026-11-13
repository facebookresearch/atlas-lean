/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Triangles in graphs just above the Turán number (Erdős Problem 1010)

Erdős Problem 1010: let `t < ⌊n / 2⌋`. Does every graph on `n` vertices with `⌊n² / 4⌋ + t` edges
contain at least `t ⌊n / 2⌋` triangles?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.TrianglesAboveTuranThresholdErdosProblem1010Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1010, https://www.erdosproblems.com/1010 (status
PROVED). UnsolvedMath record UM-30007124 (`EP-1010`), dataset ulamai/UnsolvedMath v1.8.0.

Triangles are the `3`-cliques (`cliqueSet 3`), counted with `Set.ncard`; the edge count is exactly
`⌊n² / 4⌋ + t` as in the source (a graph with more edges contains such a subgraph). Compared with
the formal-conjectures statement `ErdosProblems/1010.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 1010: for `t < ⌊n / 2⌋`, every graph on `n` vertices with `⌊n² / 4⌋ + t` edges has
at least `t ⌊n / 2⌋` triangles. -/
def trianglesAboveTuranThreshold : Prop :=
  ∀ n t : ℕ, t < n / 2 → ∀ G : SimpleGraph (Fin n),
    G.edgeSet.ncard = n ^ 2 / 4 + t → t * (n / 2) ≤ (G.cliqueSet 3).ncard

/--
Resolved true: proved independently by Lovász and Simonovits and by Nikiforov and Khadzhiivanov;
erdosproblems.com/1010 lists the problem as proved, with a formal proof in plby/lean-proofs
(`Erdos1010.lean`). Source: T. F. Bloom, Erdős Problems, Problem #1010,
https://www.erdosproblems.com/1010 (status PROVED); resolution: L. Lovász and M. Simonovits, On the
number of complete subgraphs of a graph (1976), 431-441; V. S. Nikiforov and N. G. Khadzhiivanov,
Solution of the problem of P. Erdős on the number of triangles in graphs with n vertices and [n²/4]
+ l edges, C. R. Acad. Bulgare Sci. (1981), 969-970, affirmative answer, proved independently
(erdosproblems.com/1010),
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1010.lean#L612.
-/
public theorem_wanted trianglesAboveTuranThreshold_holds : trianglesAboveTuranThreshold

end MathlibExt.GraphTheory.TrianglesAboveTuranThresholdErdosProblem1010Wanted
