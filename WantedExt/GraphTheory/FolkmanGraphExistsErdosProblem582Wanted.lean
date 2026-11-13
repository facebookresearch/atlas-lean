/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# `K₄`-free graphs that arrow the triangle (Erdős Problem 582)

Erdős Problem 582 (Erdős and Hajnal): does there exist a graph `G` which contains no `K₄`, and yet
any `2`-colouring of the edges produces a monochromatic `K₃`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.FolkmanGraphExistsErdosProblem582Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #582, https://www.erdosproblems.com/582 (status PROVED
(LEAN)). UnsolvedMath record UM-30006940 (`EP-582`), dataset ulamai/UnsolvedMath v1.8.0.

The graph is finite (on `Fin n`), which makes the existence claim stronger; a colouring is a red
subgraph `R ≤ G` with blue edges `G \ R`, and a monochromatic triangle is a triangle of `R` or of `G
\ R`. Compared with the formal-conjectures statement `ErdosProblems/582.lean` (equivalent; no code
imported).
-/

/-- Erdős Problem 582 (Erdős and Hajnal): there is a finite `K₄`-free graph `G` such that every
red/blue colouring of its edges (red edges `R ≤ G`, blue edges `G \ R`) has a monochromatic
triangle. -/
def kFourFreeEdgeRamseyForTriangles : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 4 ∧
    ∀ R ≤ G, ¬ R.CliqueFree 3 ∨ ¬ (G \ R).CliqueFree 3

/--
Resolved true: Folkman proved that such graphs exist; the least number of vertices of one lies
between `21` (Bikov and Nenov) and `786` (Lange, Radziszowski and Xu); erdosproblems.com/582 lists
the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #582,
https://www.erdosproblems.com/582 (status PROVED (LEAN)); resolution: J. Folkman, Graphs with
monochromatic complete subgraphs in every edge coloring, SIAM J. Appl. Math. (1970), 19-24,
erdosproblems.com/582: existence proved by Folkman; the least order N of such a graph satisfies 21 ≤
N ≤ 786 (Bikov and Nenov 2020; Lange, Radziszowski and Xu 2014), https://www.erdosproblems.com/582.
-/
public theorem_wanted kFourFreeEdgeRamseyForTriangles_holds : kFourFreeEdgeRamseyForTriangles

end MathlibExt.GraphTheory.FolkmanGraphExistsErdosProblem582Wanted
