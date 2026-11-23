/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDUCED MATCHING ON BIPARTITE GRAPHS is NP-complete

Source:
K. Cameron, "Induced matchings", Discrete Applied Mathematics 24 (1989), 97-102,
doi:10.1016/0166-218X(92)90275-F;
L. J. Stockmeyer and V. V. Vazirani, "NP-completeness of some generalizations of the maximum
matching problem", Information Processing Letters 15 (1982), 14-19,
doi:10.1016/0020-0190(82)90077-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MaximumInducedMatchingWanted
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumInducedMatchingBipartite

/-!
# INDUCED MATCHING ON BIPARTITE GRAPHS is NP-complete

INSTANCE: a bipartite graph `G = (V, E)` and a positive integer `K`. QUESTION: does `G` have an
induced matching of at least `K` edges, that is, a set of pairwise disjoint edges no two of which
are joined by an edge of `G`?

This is the restriction of `WantedExt.Complexity.NPComplete.MaximumInducedMatchingWanted` to
bipartite graphs, the class for which Stockmeyer and Vazirani and Cameron prove NP-completeness
(that module's docstring records Cameron's bipartite result). The instance type, the parent
well-formedness condition and the question are that module's
(`MaximumInducedMatching.MaximumInducedMatchingInstance`, `MaximumInducedMatching.WellFormed`,
`MaximumInducedMatching.MaximumInducedMatchingFeasible`); the restriction is added to
`WellFormed`: the graph of the edge list (`Cslib.Complexity.Karp.edgeGraph`) is bipartite in the
sense of Mathlib's `SimpleGraph.IsBipartite` (2-colorability), and `K` is positive, as in the
source's instance (the parent's well-formedness does not require it).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: it is a well-formed MAXIMUM INDUCED MATCHING instance
(simple edge list), its graph is bipartite, and `K` is positive. -/
def WellFormed (i : MaximumInducedMatching.MaximumInducedMatchingInstance) : Prop :=
  MaximumInducedMatching.WellFormed i ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsBipartite ∧ 0 < i.2.2

open Classical in
/-- INDUCED MATCHING ON BIPARTITE GRAPHS as a decision problem over bitstrings. -/
noncomputable def maximumInducedMatchingBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumInducedMatching.MaximumInducedMatchingInstance) x with
  | some i => decide (WellFormed i ∧ MaximumInducedMatching.MaximumInducedMatchingFeasible i)
  | none => false

/-- **INDUCED MATCHING is NP-complete on bipartite graphs.** Source: Cameron (1989);
Stockmeyer and Vazirani (1982). -/
public theorem_wanted maximumInducedMatchingBipartite_npComplete :
    maximumInducedMatchingBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumInducedMatchingBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.MaximumInducedMatchingBipartite
