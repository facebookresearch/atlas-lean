/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Large independent sets in every subgraph bound the chromatic number (Erdős Problem 922)

Erdős Problem 922: let `k ≥ 0`. Let `G` be a graph such that every subgraph `H` contains an
independent set of size `≥ (n - k)/2`, where `n` is the number of vertices of `H`. Must `G` have
chromatic number at most `k + 2`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

namespace MathlibExt.GraphTheory.IndependentSetsChromaticBoundErdosProblem922Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #922, https://www.erdosproblems.com/922 (status
PROVED). UnsolvedMath record UM-30007089 (`EP-922`), dataset ulamai/UnsolvedMath v1.8.0.

Finite graphs (`V : Type` with `Fintype V`). A subgraph on a vertex set `S` has at least the
independent sets of the induced subgraph on `S`, so the hypothesis for all subgraphs is the same as
for all vertex sets `S`, which is how it is stated; `|I| ≥ (|S| - k)/2` is written `|S| - k ≤ 2|I|`
in `ℤ`, and chromatic number at most `k + 2` is `G.Colorable (k + 2)`. Compared with the
formal-conjectures statement `ErdosProblems/922.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 922: for every `k ≥ 0`, a finite graph in which every set of `h` vertices
contains an independent set of size at least `(h - k) / 2` has chromatic number at most `k + 2`.
(Independent sets of a subgraph on a vertex set `S` include those of the induced subgraph on `S`,
so it suffices to require the bound for induced subgraphs.) -/
def chromaticBoundFromIndependentSets : Prop :=
  ∀ (k : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V),
    (∀ S : Finset V, ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧ (S.card : ℤ) - k ≤ 2 * I.card) →
      G.Colorable (k + 2)

/--
Resolved true: Folkman proved that a graph in which every subgraph on `h` vertices has an
independent set of size at least `(h - k)/2` has chromatic number at most `k + 2` (Erdős and Hajnal
could not prove the case `k = 1`); erdosproblems.com/922 lists the problem as proved. Source: T. F.
Bloom, Erdős Problems, Problem #922, https://www.erdosproblems.com/922 (status PROVED); resolution:
J. H. Folkman, An upper bound on the chromatic number of a graph (1970), 437-457,
erdosproblems.com/922: 'This is true, and was proved by Folkman', https://www.erdosproblems.com/922.
-/
public theorem_wanted chromaticBoundFromIndependentSets_holds : chromaticBoundFromIndependentSets

end MathlibExt.GraphTheory.IndependentSetsChromaticBoundErdosProblem922Wanted
