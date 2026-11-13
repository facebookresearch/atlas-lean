/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bipartite plus low-degree decompositions (Erdős Problem 613)

Erdős Problem 613: let `n ≥ 3` and `G` be a graph with `C(2n+1, 2) - C(n, 2) - 1` edges. Must `G` be
the union of a bipartite graph and a graph with maximum degree less than `n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

@[expose] public section

namespace MathlibExt.GraphTheory.BipartitePlusLowDegreeErdosProblem613Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #613, https://www.erdosproblems.com/613 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006951 (`EP-613`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are finite, on `Fin m` for any `m`; the union is `G = B ⊔ D` with `B.IsBipartite` and every
vertex of degree less than `n` in `D`. Equivalently the problem asks whether `r̂(K_{1,n}, 𝓕) =
C(2n+1, 2) - C(n, 2)` for the size Ramsey number of the star `K_{1,n}` versus the family `𝓕` of odd
cycles. Compared with the formal-conjectures statement `ErdosProblems/613.lean` (equivalent; no code
imported).
-/

/-- Erdős Problem 613 (Faudree's conjecture, in Erdős' form): for `n ≥ 3`, every graph with exactly
`C(2n+1, 2) - C(n, 2) - 1` edges is the union of a bipartite graph and a graph of maximum degree
less than `n`. -/
def bipartitePlusLowDegreeDecomposition : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ (m : ℕ) (G : SimpleGraph (Fin m)),
    G.edgeSet.ncard = (2 * n + 1).choose 2 - n.choose 2 - 1 →
      ∃ B D : SimpleGraph (Fin m), G = B ⊔ D ∧ B.IsBipartite ∧
        ∀ v, (D.neighborSet v).ncard < n

/--
Resolved false: Pikhurko constructed graphs with fewer than `n² + √2 n^{3/2} + n` edges that are not
the union of a bipartite graph and a graph of maximum degree less than `n` (adding edges keeps this
property); for `n = 5` his construction has exactly `44 = C(11, 2) - C(5, 2) - 1` edges.
erdosproblems.com/613 lists the problem as disproved (the case `n = 5` was formalized by Tao).
Source: T. F. Bloom, Erdős Problems, Problem #613, https://www.erdosproblems.com/613 (status
DISPROVED (LEAN)); resolution: O. Pikhurko, Size Ramsey numbers of stars versus 3-chromatic graphs,
Combinatorica (2001), 403-412, abstract: n² + (0.577 + o(1)) n^{3/2} < r̂(K_{1,n}, C_odd) < n² + √2
n^{3/2} + n, the upper (constructive) bound disproving Erdős' conjecture; p. 405: the conjecture
fails already for n = 5 (a graph with 44 edges, against the conjectured value 45),
https://pikhurko.github.io/E/Pikhurko01c.pdf.
-/
public theorem_wanted bipartitePlusLowDegreeDecomposition_refuted :
    ¬ bipartitePlusLowDegreeDecomposition

end MathlibExt.GraphTheory.BipartitePlusLowDegreeErdosProblem613Wanted
