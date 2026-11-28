/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM FIXED-LENGTH DISJOINT PATHS with fixed `K ≥ 4` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND42] MAXIMUM FIXED-LENGTH DISJOINT PATHS,
p. 218, comment ("Remains NP-complete for fixed K ≥ 4");
A. Itai, Y. Perl and Y. Shiloach, "The complexity of finding maximum disjoint paths with length
constraints", Networks 12(3) (1982), 277-286, doi:10.1002/net.3230120306.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaximumFixedLengthDisjointPathsFixedKDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumFixedLengthDisjointPathsFixedK

open MetaMathlibExt.Complexity.NPComplete.MaximumFixedLengthDisjointPaths

/-!
# MAXIMUM FIXED-LENGTH DISJOINT PATHS with fixed `K ≥ 4` is NP-complete

For a fixed constant `K ≥ 4`: given a graph `G = (V, E)`, specified vertices `s` and `t`, and a
positive integer `J ≤ |V|`, does `G` contain `J` or more mutually vertex-disjoint paths from `s`
to `t`, each involving exactly `K` edges?

This is MAXIMUM FIXED-LENGTH DISJOINT PATHS
(`WantedExt.Complexity.NPComplete.MaximumFixedLengthDisjointPathsWanted`) with `K` no longer
part of the instance. The instance is the graph, `s`, `t` and `J`, and `withLength i K` appends
the fixed `K` to obtain an instance of that problem, whose `WellFormed` (simple edge list,
`s ≠ t`, `0 < J ≤ |V|`, `0 < K ≤ |V|`) and question (`J` distinct paths of length exactly `K`,
pairwise `SimpleGraph.InternallyDisjoint`) are reused unchanged. For fixed `K`, the condition
`K ≤ |V|` only excludes the finitely many graphs with fewer than `K` vertices.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM FIXED-LENGTH DISJOINT PATHS is NP-complete for every fixed `K ≥ 4`.** Source:
Garey and Johnson (1979), [ND42], comment; Itai, Perl and Shiloach (1982). -/
public theorem_wanted maximumFixedLengthDisjointPathsFixedK_npComplete (K : ℕ) (hK : 4 ≤ K) :
    fixedLengthDec K ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (fixedLengthDec K)

end MetaMathlibExt.Complexity.NPComplete.MaximumFixedLengthDisjointPathsFixedK
