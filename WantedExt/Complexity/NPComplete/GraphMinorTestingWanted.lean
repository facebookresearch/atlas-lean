/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH MINOR TESTING is NP-complete

Source:
J. Matoušek and R. Thomas, "On the complexity of finding iso- and other morphisms for partial
k-trees", Discrete Mathematics 108 (1992), 343-364, doi:10.1016/0012-365X(92)90687-B (minor
containment is NP-complete, even for trees of bounded diameter);
T. Gima, S. Kumabe, K. Kurita, Y. Okada and Y. Otachi, "Dichotomies for tree minor containment
with structural parameters", in *WALCOM: Algorithms and Computation*, Lecture Notes in Computer
Science 14549, Springer (2024), 392-405, doi:10.1007/978-981-97-0566-5_28 (Section 1.2 records
the result of Matoušek and Thomas; arXiv:2311.03225).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GraphMinorTestingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphMinorTesting

/-!
# GRAPH MINOR TESTING is NP-complete

INSTANCE: graphs `G` and `H`.
QUESTION: is `H` a minor of `G`, that is, can a graph isomorphic to `H` be obtained from `G` by
deleting vertices, deleting edges and contracting edges?

Both graphs are part of the input (for each fixed `H` the problem is solvable in polynomial
time by the Robertson-Seymour theory). Matoušek and Thomas proved the problem NP-complete, even
when both graphs are trees of bounded diameter; when `H` is a cycle with as many vertices as `G`
it is HAMILTONIAN CIRCUIT. A certificate is a minor model: disjoint connected branch sets of
`G`, one per vertex of `H`, with an edge of `G` between the branch sets of every edge of `H`.

The minor relation is MathlibExt's `MetaMathlibExt.IsMinor`, from the module
`MathlibExt.Combinatorics.Graph.GraphMinor`: the reflexive-transitive closure of isomorphism,
single-vertex deletion,
single-edge deletion and single-edge contraction, on bundled finite graphs
(`MetaMathlibExt.FinGraph`). Each graph is given by its vertex count `n` (vertices `Fin n`) and
an edge list, as a `Cslib.Complexity.Karp.edgeGraph`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH MINOR TESTING is NP-complete.** Source: Matoušek and Thomas (1992); Gima, Kumabe,
Kurita, Okada and Otachi (2024), Section 1.2. -/
public theorem_wanted graphMinorTesting_npComplete :
    graphMinorTestingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphMinorTestingDec

end MetaMathlibExt.Complexity.NPComplete.GraphMinorTesting
