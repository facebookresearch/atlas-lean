/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED OPTIMAL LINEAR ARRANGEMENT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT43] DIRECTED OPTIMAL LINEAR
ARRANGEMENT (reference: [Even and Shiloach, 1975], transformation from OPTIMAL LINEAR
ARRANGEMENT); S. Even and Y. Shiloach, "NP-completeness of several arrangement problems",
Technical Report 43, Department of Computer Science, Technion, Haifa (1975) (not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DirectedOptimalLinearArrangementDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedOptimalLinearArrangement

/-!
# DIRECTED OPTIMAL LINEAR ARRANGEMENT is NP-complete

INSTANCE: a directed graph `G = (V, A)` and a positive integer `K`.
QUESTION: is there a one-to-one function `f : V → {1, 2, …, |V|}` such that `f(u) < f(v)`
whenever `(u, v) ∈ A` and such that `∑_{(u, v) ∈ A} (f(v) - f(u)) ≤ K`?

Garey and Johnson's [GT43], attributed to Even and Shiloach (by a transformation from OPTIMAL
LINEAR ARRANGEMENT, [GT42]). The vertices are `0, …, n - 1` and the arcs a list of ordered pairs
without repetitions or loops (a directed graph); antiparallel arcs `(u, v)`, `(v, u)` are allowed
by the definition and make the instance a no-instance. A one-to-one `f` is the position in a
permutation `perm` of `List.range n` (`List.idxOf`); positions `0, …, n - 1` instead of
`1, …, |V|` change no difference. Every arc must go forward, `idxOf u < idxOf v`, so each term
`f(v) - f(u)` is a positive natural number. `WellFormed` requires Garey and Johnson's `0 < K`.

Membership in NP: the permutation is a certificate. Isolated vertices (outside the arc list) can
be placed last without changing any arc, so the binary vertex count does not make the problem
succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DIRECTED OPTIMAL LINEAR ARRANGEMENT is NP-complete.** Source: Garey and Johnson (1979),
[GT43]; Even and Shiloach (1975). -/
public theorem_wanted directedOptimalLinearArrangement_npComplete :
    directedOptimalLinearArrangementDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedOptimalLinearArrangementDec

end MetaMathlibExt.Complexity.NPComplete.DirectedOptimalLinearArrangement
