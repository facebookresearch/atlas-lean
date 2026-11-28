/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED MAXIMUM LENGTH-BOUNDED DISJOINT PATHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND41] MAXIMUM
LENGTH-BOUNDED DISJOINT PATHS, p. 217, comment ("The same results hold if G is a directed
graph and the paths must be directed paths");
A. Itai, Y. Perl, and Y. Shiloach, "The complexity of finding maximum disjoint
paths with length constraints", Networks 12 (1982), 277-286,
doi:10.1002/net.3230120306.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DirectedMaximumLengthBoundedDisjointPathsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedMaximumLengthBoundedDisjointPaths

/-!
# DIRECTED MAXIMUM LENGTH-BOUNDED DISJOINT PATHS is NP-complete

INSTANCE: a directed graph `G = (V, A)`, specified vertices `s` and `t`, and positive integers
`J, K ≤ |V|`. QUESTION: does `G` contain `J` or more mutually vertex-disjoint directed paths
from `s` to `t`, none involving more than `K` arcs?

This is MAXIMUM LENGTH-BOUNDED DISJOINT PATHS ([ND41],
`WantedExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPathsWanted`) for directed graphs
and directed paths. The vertices are `0, ..., n - 1` and the arcs are a list of ordered pairs
without repetitions or self-loops; `s` and `t` are distinct, as in Itai, Perl, and Shiloach
("a graph G with two distinct vertices s and t"). A directed path from `s` to `t` is
`IsDirectedPath` from `WantedExt.Complexity.NPComplete.DirectedTwoDisjointConnectingPathsWanted`:
a list of pairwise distinct vertices that starts at `s`, ends at `t`, and has an arc from each
vertex to the next. Its number of arcs is one less than the length of the list. Mutually
vertex-disjoint paths from `s` to `t` share no vertex other than `s` and `t`. The family is
indexed by `Fin J` and required to be injective, so it consists of `J` different paths; without
that, the single path along an arc `(s, t)` could be repeated `J` times, since it has no inner
vertex. "`J` or more" paths is the same as `J` paths, because a subfamily of a disjoint family
is disjoint.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open DirectedTwoDisjointConnectingPaths (IsDirectedPath)

/-- **DIRECTED MAXIMUM LENGTH-BOUNDED DISJOINT PATHS is NP-complete.** Source: Garey and Johnson
(1979), [ND41], comment; Itai, Perl, and Shiloach (1982). -/
public theorem_wanted directedMaximumLengthBoundedDisjointPaths_npComplete :
    directedMaximumLengthBoundedDisjointPathsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedMaximumLengthBoundedDisjointPathsDec

end MetaMathlibExt.Complexity.NPComplete.DirectedMaximumLengthBoundedDisjointPaths
