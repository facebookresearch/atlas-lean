/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Dense small sets in graphs with small independence number (Alon's theorem, Erdős Problem 801)

Erdős Problem 801: if `G` is a graph on `n` vertices containing no independent set on more than
`n^{1/2}` vertices, then there is a set of at most `n^{1/2}` vertices containing `≫ n^{1/2} log n`
edges. This file states Alon's theorem on the problem, not the problem as posed: Alon assumes
independence number smaller than `⌊√n⌋`, while the problem also allows independence number exactly
`⌊√n⌋`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.LowIndependenceDenseSubsetErdosProblem801Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #801, https://www.erdosproblems.com/801 (status
PROVED). UnsolvedMath record UM-30007040 (`EP-801`), dataset ulamai/UnsolvedMath v1.8.0.

Alon's Theorem 1.2 assumes that every set of `⌊√n⌋` vertices spans an edge (every independent set
has fewer than `⌊√n⌋` vertices) and finds `⌊√n⌋` vertices spanning `Ω(√n log n)` edges; the target
is this theorem, a strict-boundary variant rather than the problem itself. The page's 'no
independent set on more than `n^{1/2}` vertices' also admits graphs whose independence number is
exactly `⌊√n⌋`, which Alon's theorem does not cover; the problem in that form is not formalized
here. The edges spanned by `S` are those of the induced subgraph `G[S]`; the logarithm is natural
(Alon's base `2` changes only the constant). formal-conjectures' `ErdosProblems/801.lean` states the
page's form (independence number at most `√n`); no code imported.
-/

/-- Alon's theorem (Theorem 1.2), the strict-boundary variant of Erdős Problem 801 rather than the
problem as posed: there is `c > 0` such that for all large `n`, every graph on `n` vertices in
which every set of `⌊√n⌋` vertices spans an edge (every independent set has fewer than `⌊√n⌋`
vertices) has a set of at most `⌊√n⌋` vertices spanning at least `c √n log n` edges. -/
def lowIndependenceDenseSmallSet : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph (Fin n),
    (∀ s : Finset (Fin n), G.IsIndepSet (s : Set (Fin n)) → s.card < Nat.sqrt n) →
      ∃ S : Finset (Fin n), S.card ≤ Nat.sqrt n ∧
        c * Real.sqrt n * Real.log n ≤ (G.induce (S : Set (Fin n))).edgeSet.ncard

/--
Resolved true: this is Alon's Theorem 1.2: if every set of `⌊√n⌋` vertices spans an edge then some
`⌊√n⌋` vertices span `Ω(√n log n)` edges. erdosproblems.com/801 lists the problem as proved by Alon;
its form with independence number at most `⌊√n⌋` is not stated here.
Source: T. F. Bloom, Erdős Problems, Problem #801, https://www.erdosproblems.com/801 (status
PROVED); resolution: N. Alon, Independence numbers of locally sparse graphs and a Ramsey type
problem, Random Structures Algorithms 9 (1996), 271-278, Theorem 1.2: if a graph on n vertices has
independence number smaller than ⌊√n⌋ (any ⌊√n⌋ vertices span an edge), some set of ⌊√n⌋ vertices
spans Ω(√n log n) edges; this is tight and settles a problem of Erdős (conjectured in 1979),
https://web.math.princeton.edu/~nalon/PDFS/indrams1.pdf.
-/
public theorem_wanted lowIndependenceDenseSmallSet_holds : lowIndependenceDenseSmallSet

end MathlibExt.GraphTheory.LowIndependenceDenseSubsetErdosProblem801Wanted
