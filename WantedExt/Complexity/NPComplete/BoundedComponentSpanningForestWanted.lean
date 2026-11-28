/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED COMPONENT SPANNING FOREST is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND10] BOUNDED COMPONENT SPANNING
FOREST; F. O. Hadlock, "Minimum spanning forests of bounded trees", Proceedings of the 5th
Southeastern Conference on Combinatorics, Graph Theory and Computing, Utilitas Mathematica
(1974), 449-460; M. E. Dyer and A. M. Frieze, "On the complexity of partitioning graphs into
connected subgraphs", Discrete Applied Mathematics 10 (1985), 139-153,
doi:10.1016/0166-218X(85)90008-3.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BoundedComponentSpanningForestDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedComponentSpanningForest

/-!
# BOUNDED COMPONENT SPANNING FOREST is NP-complete

INSTANCE: a graph `G = (V, E)`, a weight `w(v) ∈ ℤ₀⁺` for each `v ∈ V`, and positive integers
`K ≤ |V|` and `B`. QUESTION: can the vertices in `V` be partitioned into `k ≤ K` disjoint sets
`V₁, ..., V_k` such that, for `1 ≤ i ≤ k`, the subgraph of `G` induced by `Vᵢ` is connected and
the sum of the weights of the vertices in `Vᵢ` does not exceed `B`?

The partition is a surjective block map `c : Fin n → Fin k` (parts are nonempty, as Mathlib's
`SimpleGraph.Connected` requires); each part induces a connected subgraph (`SimpleGraph.induce`)
and has weight at most `B`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BOUNDED COMPONENT SPANNING FOREST is NP-complete.** Source: Garey and Johnson (1979),
[ND10]; Hadlock (1974); Dyer and Frieze (1985). -/
public theorem_wanted boundedComponentSpanningForest_npComplete :
    boundedComponentSpanningForestDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L boundedComponentSpanningForestDec

end MetaMathlibExt.Complexity.NPComplete.BoundedComponentSpanningForest
