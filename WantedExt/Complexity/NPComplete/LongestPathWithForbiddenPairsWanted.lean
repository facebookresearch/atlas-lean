/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST PATH WITH FORBIDDEN PAIRS is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), entry LONGEST PATH WITH FORBIDDEN PAIRS in its graph theory section (decision version;
the entry gives the Garey-Johnson code GT54), related to
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT54] PATH WITH FORBIDDEN PAIRS;
H. N. Gabow, S. N. Maheshwari and L. J. Osterweil, "On two problems in the generation of program
test paths", IEEE Transactions on Software Engineering SE-2(3) (1976), 227-231,
doi:10.1109/TSE.1976.233819;
Garey and Johnson (1979), [GT39] HAMILTONIAN PATH (the case with no pairs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LongestPathWithForbiddenPairsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestPathWithForbiddenPairs

/-!
# LONGEST PATH WITH FORBIDDEN PAIRS is NP-complete

INSTANCE: a graph `G = (V, E)`, a collection `C = {(a₁, b₁), …, (aₘ, bₘ)}` of pairs of vertices
from `V`, and a positive integer `K`.
QUESTION: is there a simple path in `G` that contains at most one vertex from each pair in `C`
and has at least `K` edges?

This is the decision version of the compendium's LONGEST PATH WITH FORBIDDEN PAIRS (undirected
graph, no prescribed endpoints, measure the number of edges of the path), the optimization
counterpart of Garey and Johnson's PATH WITH FORBIDDEN PAIRS ([GT54],
`PathWithForbiddenPairsWanted`, a directed `s`-`t` path, NP-complete by Gabow, Maheshwari and
Osterweil). With `C` empty, `|V| ≥ 2` and `K = |V| - 1` the question asks for a Hamiltonian path,
which is NP-complete ([GT39]); a reduction from HAMILTONIAN PATH decides graphs with at most one
vertex directly and maps them to a fixed yes- or no-instance. So the problem is NP-hard in the
strong sense; an explicit path is a certificate for membership in NP.

The vertices are `0, …, n - 1`; the edges are a simple edge list (no loops, no repeated edge in
either orientation, endpoints below `n`), as in `LongestPathWanted`, and the pairs are a list of
pairs of vertices below `n`. A simple path is a nonempty list of distinct vertices below `n` in
which consecutive vertices are joined by an edge (`List.IsChain`); its number of edges is its
length minus one. "At most one vertex from each pair" means, as in
`PathWithForbiddenPairsWanted`, that a path containing both `aⱼ` and `bⱼ` has `aⱼ = bⱼ`.
`WellFormed` requires `0 < K` (the source's "positive integer K").

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LONGEST PATH WITH FORBIDDEN PAIRS is NP-complete.** Source: Crescenzi and Kann, LONGEST
PATH WITH FORBIDDEN PAIRS; Garey and Johnson (1979), [GT54], [GT39]. -/
public theorem_wanted longestPathWithForbiddenPairs_npComplete :
    longestPathWithForbiddenPairsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L longestPathWithForbiddenPairsDec

end MetaMathlibExt.Complexity.NPComplete.LongestPathWithForbiddenPairs
