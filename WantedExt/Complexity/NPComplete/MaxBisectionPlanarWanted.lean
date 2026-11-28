/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM BISECTION on planar graphs is NP-complete

Source:
K. Jansen, M. Karpinski, A. Lingas, and E. Seidel, "Polynomial time approximation schemes for
MAX-BISECTION on planar and geometric graphs", SIAM Journal on Computing 35 (2005), 110-119,
doi:10.1137/S009753970139567X (NP-hardness of exact MAX-BISECTION on planar graphs, credited
there to M. Jerrum, personal communication);
J. Díaz and M. Kamiński, "MAX-CUT and MAX-BISECTION are NP-hard on unit disk graphs",
Theoretical Computer Science 377 (2007), 271-276, doi:10.1016/j.tcs.2007.02.013 (records the
result: "max-bisection remains NP-hard on planar graphs (result of Jerrum presented in [JKLS])");
ISGCI, class "planar" (gc_43), problem Maximum bisection, NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaxBisectionPlanarDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxBisectionPlanar

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance)

/-!
# MAXIMUM BISECTION on planar graphs is NP-complete

INSTANCE: a planar graph `G = (V, E)` and a positive integer `K`.
QUESTION: is there a partition of `V` into sets `A`, `B` with `|A| = |B|` (or `|A| = |B| - 1`
when `|V|` is odd) such that at least `K` edges join `A` and `B`?

This is MAXIMUM BISECTION (Jansen, Karpinski, Lingas and Seidel: a partition of the vertices
into two equal size subsets maximizing the number of edges with endpoints in both) restricted to
planar graphs, in the ISGCI formulation, which also admits odd `|V|` with parts of sizes
`⌊|V| / 2⌋` and `⌈|V| / 2⌉`; for even `|V|` it is the equal-size bisection of the sources.
Jansen et al. report that Jerrum established NP-hardness of exact MAX-BISECTION on planar
graphs, in contrast to MAX-CUT, which is polynomial on planar graphs; Díaz and Kamiński record
the same result. Membership in NP: isolated vertices can go to either side, so a partition of
the non-isolated vertices with the side sizes checked arithmetically is a certificate.

The instance, the simple-edge-list conditions and the crossing-edge count are those of MAXIMUM
CUT (`CSLibExt.Complexity.NPComplete.MaxCutDefs`); the question adds `|A| = ⌊|V| / 2⌋` for the
side `A = S`, the bisection condition of `MinBisectionWanted`. Planarity is the repository's
`SimpleGraph.IsPlanar` (a crossing-free straight-line drawing, which by Fáry's theorem exists
exactly for planar graphs) of `Cslib.Complexity.Karp.edgeGraph`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM BISECTION on planar graphs is NP-complete.** Source: Jansen, Karpinski, Lingas,
and Seidel (2005) (Jerrum); Díaz and Kamiński (2007); ISGCI (gc_43). -/
public theorem_wanted maxBisectionPlanar_npComplete :
    maxBisectionPlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maxBisectionPlanarDec

end MetaMathlibExt.Complexity.NPComplete.MaxBisectionPlanar
