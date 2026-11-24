/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bipartite Ramanujan graphs of every degree (wanted)

Arbitrarily large `d`-regular bipartite Ramanujan graphs exist for every `d ≥ 3` (Marcus,
Spielman and Srivastava, *Interlacing families I: bipartite Ramanujan graphs of all degrees*,
Ann. of Math. 182 (2015), arXiv:1304.4132, Theorem 5.5). The proof takes repeated 2-lifts of the
complete bipartite graph `K_{d,d}`, choosing each signing through an interlacing family of
characteristic polynomials of signed adjacency matrices.
-/

@[expose] public section

namespace MathlibExt.GraphTheory.RamanujanGraphsWanted

open Classical in
/-- **Bipartite Ramanujan graphs of every degree.** For every `d ≥ 3` there are arbitrarily large
`d`-regular bipartite Ramanujan graphs: `d`-regular bipartite graphs whose adjacency eigenvalues,
other than the largest (`d`) and the smallest (`-d`), all lie in `[-2√(d - 1), 2√(d - 1)]`
(Marcus, Spielman and Srivastava, *Interlacing families I: bipartite Ramanujan graphs of all
degrees*, arXiv:1304.4132, Theorem 5.5, with the definition of Section 2.1). -/
theorem_wanted exists_bipartite_ramanujan (d : ℕ) (hd : 3 ≤ d) (N : ℕ) :
    ∃ n ≥ N, ∃ G : SimpleGraph (Fin n), G.IsRegularOfDegree d ∧ G.Colorable 2 ∧
      ∀ i : Fin (Fintype.card (Fin n)), (i : ℕ) ≠ 0 → (i : ℕ) + 1 ≠ n →
        |(G.isHermitian_adjMatrix (R := ℝ)).eigenvalues₀ i| ≤ 2 * Real.sqrt ((d : ℝ) - 1)

end MathlibExt.GraphTheory.RamanujanGraphsWanted
