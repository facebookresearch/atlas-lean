/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR 3SAT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO1] SATISFIABILITY, comment
(PLANAR 3SAT, attributed to Lichtenstein, 1977);
D. Lichtenstein, "Planar formulae and their uses", SIAM Journal on Computing 11(2) (1982),
329-343, doi:10.1137/0211025.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PlanarThreeSatDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarThreeSat

/-!
# PLANAR 3SAT is NP-complete

INSTANCE: a set `U` of variables and a collection `C` of clauses over `U` such that each
`c ∈ C` has `|c| ≤ 3` and the bipartite graph `G = (V, E)`, where `V = U ∪ C` and `E` contains
exactly those pairs `{u, c}` such that either `u` or `ū` belongs to the clause `c`, is planar.
QUESTION: is there a satisfying truth assignment for `C`?

This is SATISFIABILITY restricted as in Garey and Johnson's comment to [LO1] (Lichtenstein
1977; published as Lichtenstein 1982). The formula uses the repository's CNF representation
(`Cslib.Logic.LegacyPL.CNF`): a list of clauses, each a list of literals `(variable, polarity)`,
with variables `0, …, n - 1`; `|c| ≤ 3` is `c.length ≤ 3`, as in the repository's 3SAT
(`Cslib.Complexity.Karp.is3`). The graph `G` has one vertex `Sum.inl u` for each variable
`u` and one vertex `Sum.inr c` for each clause `c` of the list, and `Sum.inl u` is adjacent to
`Sum.inr c` exactly when some literal of `c` has variable `u`. Planarity is the shared
MathlibExt predicate `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing; by Fáry's
theorem this is planarity for finite simple graphs).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PLANAR 3SAT is NP-complete.** Source: Garey and Johnson (1979), [LO1], comment;
Lichtenstein (1982). -/
public theorem_wanted planarThreeSat_npComplete :
    planarThreeSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarThreeSatDec

end MetaMathlibExt.Complexity.NPComplete.PlanarThreeSat
