/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRAVELING SALESMAN WITH TIME WINDOWS: FEASIBILITY is NP-complete

Source:
M. W. P. Savelsbergh, "Local search in routing problems with time windows", Annals of
Operations Research 4 (1985), 285-305, doi:10.1007/BF02022044;
M. W. P. Savelsbergh, *Computer Aided Routing*, CWI Tract 75, Centrum voor Wiskunde en
Informatica, Amsterdam (1992), Section 4.1, pp. 19-20 (the statement and proof: "The problem
of determining whether there exists a feasible tour for the TSPTW is NP-complete in the strong
sense").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TspTimeWindowsFeasibilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TspTimeWindowsFeasibility

/-!
# TRAVELING SALESMAN WITH TIME WINDOWS: FEASIBILITY is NP-complete

INSTANCE: vertices `V = {0, …, n + 1}`, a travel time `t_ij ∈ ℕ` for each `(i, j) ∈ V × V`,
where the matrix `(t_ij)` is symmetric and satisfies the triangle inequality, and for each
vertex `i` a time window `[e_i, l_i]`, where `e_i` is the earliest and `l_i` the latest service
time. QUESTION: is there a feasible tour, i.e. a path from the origin `0` to the
destination `n + 1` that visits each vertex exactly once, together with service (departure)
times `D_i` with `e_i ≤ D_i ≤ l_i` for every vertex and `D_i + t_ij ≤ D_j` whenever `j`
immediately follows `i` on the path?

This is Savelsbergh's TSPTW (1985; CWI Tract 75, Sections 1 and 4.1): service at `i` must take
place within its window, the service time is included in the travel time, and a vehicle that
arrives before `e_i` waits, which is why consecutive service times need only satisfy
`D_i + t_ij ≤ D_j`. The travel times are those of Savelsbergh's TSP (Section 4.1): "We assume
that the matrix (t_ij) is symmetric and satisfies the triangle inequality". Savelsbergh proves
strong NP-completeness by giving every vertex of an instance of the path version of the
traveling salesman decision problem with bound `B` the window `[0, B]`; that reduction keeps
the travel times, so it applies to the symmetric instances satisfying the triangle inequality
(for example distances `1` and `2` from HAMILTONIAN PATH between two given vertices), on which
the decision problem stays NP-complete in the strong sense. Windows and travel times are
nonnegative integers, and times are measured from `0`. The path is listed as
a permutation of `List.range (n + 2)` from `0` to `n + 1`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TRAVELING SALESMAN WITH TIME WINDOWS: FEASIBILITY is NP-complete.** Source: Savelsbergh
(1985); Savelsbergh, CWI Tract 75 (1992), Section 4.1. -/
public theorem_wanted tspTimeWindowsFeasibility_npComplete :
    tspTimeWindowsFeasibilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L tspTimeWindowsFeasibilityDec

end MetaMathlibExt.Complexity.NPComplete.TspTimeWindowsFeasibility
