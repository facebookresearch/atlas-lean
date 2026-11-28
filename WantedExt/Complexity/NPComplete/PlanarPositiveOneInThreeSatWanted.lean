/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR POSITIVE ONE-IN-THREE 3SAT is NP-complete

Source:
C. Moore and J. M. Robson, "Hard tiling problems with simple tiles", Discrete and Computational
Geometry 26 (2001), 573-590, doi:10.1007/s00454-001-0047-6 (arXiv:math/0003039), Section 3.1:
"Planar Monotone 1-in-3 SAT is NP-complete" (credited there to P. Laroche, "Planar 1-in-3
satisfiability is NP-complete", ASMICS Workshop on Tilings, ENS Lyon, 1992), and NP-complete
even when every variable occurs exactly three times.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PlanarPositiveOneInThreeSatDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarPositiveOneInThreeSat

open MetaMathlibExt.Complexity.NPComplete.OneInThreeSat
  (OneInThreeSatInstance OneInThreeSatFeasible)

/-!
# PLANAR POSITIVE ONE-IN-THREE 3SAT is NP-complete

INSTANCE: a set `U` of variables and a collection `C` of clauses over `U`, each with three
literals and none negated, such that the graph with a vertex for each variable and each clause,
and an edge joining each clause to each variable appearing in it, is planar. QUESTION: is there a
truth assignment for `U` such that each clause in `C` has exactly one true literal?

This is POSITIVE ONE-IN-THREE 3SAT (`PositiveOneInThreeSatWanted`) restricted to instances whose
variable-clause graph is planar (Moore and Robson's "Planar Monotone 1-in-3 SAT"). The instance
type and the question are those of ONE-IN-THREE 3SAT (`OneInThreeSatWanted`); `WellFormed` is
POSITIVE ONE-IN-THREE 3SAT's plus planarity of the variable-clause graph, which is PLANAR 3SAT's
`PlanarThreeSat.IncidenceGraph` (`WantedExt.Complexity.NPComplete.PlanarThreeSatWanted`, on the
same instance type): a vertex `Sum.inl u` per variable and `Sum.inr c` per clause, with `u` and
`c` adjacent exactly when some literal of `c` has variable `u`. Planarity is the repository's
`SimpleGraph.IsPlanar` (a crossing-free straight-line drawing, which by Fáry's theorem exists
exactly for the planar finite simple graphs).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PLANAR POSITIVE ONE-IN-THREE 3SAT is NP-complete.** Source: Moore and Robson (2001),
Section 3.1 (Laroche, 1992). -/
public theorem_wanted planarPositiveOneInThreeSat_npComplete :
    planarPositiveOneInThreeSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarPositiveOneInThreeSatDec

end MetaMathlibExt.Complexity.NPComplete.PlanarPositiveOneInThreeSat
