/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM LENGTH-BOUNDED EDGE-DISJOINT PATHS with `K = 4` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 217, problem [ND41] MAXIMUM
LENGTH-BOUNDED DISJOINT PATHS, comment: the edge-disjoint version is "open for `K = 4`";
A. Bley and J. Neto, "Approximability of 3- and 4-hop bounded disjoint paths problems",
Integer Programming and Combinatorial Optimization (IPCO 2010), Lecture Notes in Computer
Science 6080, Springer (2010), 205-218, doi:10.1007/978-3-642-13036-6_16, Theorem 3 and its
proof (a reduction from MAX-k-SAT(3) in which a truth assignment satisfying `r` clauses
corresponds to `6|I| + r` edge-disjoint 4-bounded paths, and conversely);
C. A. Tovey, "A simplified NP-complete satisfiability problem", Discrete Applied
Mathematics 8 (1984), 85-89, doi:10.1016/0166-218X(84)90081-7 (satisfiability with each
variable occurring at most three times is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MaximumLengthBoundedEdgeDisjointPathsFixedKWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedEdgeDisjointPathsFour

open MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedEdgeDisjointPathsFixedK

/-!
# MAXIMUM LENGTH-BOUNDED EDGE-DISJOINT PATHS with `K = 4` is NP-complete

Given a graph `G = (V, E)`, specified vertices `s` and `t`, and a positive integer `J ≤ |V|`,
does `G` contain `J` or more mutually edge-disjoint paths from `s` to `t`, none involving more
than `4` edges?

This is `fixedBoundDec 4` from
`WantedExt.Complexity.NPComplete.MaximumLengthBoundedEdgeDisjointPathsFixedKWanted`, whose
statement covers every fixed `K ≥ 5`. Garey and Johnson list `K = 4` as open; Bley and Neto
settled it: the proof of their Theorem 3 (MEDP(4) is APX-hard) builds, from a MAX-k-SAT(3)
instance with variables `I` and clauses `L`, a simple graph in which truth assignments
satisfying `r` clauses correspond to sets of `6|I| + r` edge-disjoint 4-bounded `s-t` paths in
both directions. With `J = 6|I| + |L|` this is a polynomial-time many-one reduction from
satisfiability of formulas in which every variable occurs at most three times, which is
NP-complete (Tovey).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM LENGTH-BOUNDED EDGE-DISJOINT PATHS is NP-complete for `K = 4`.** Source: Bley
and Neto (2010), Theorem 3 and its proof; Tovey (1984); Garey and Johnson (1979), [ND41],
comment (open there). -/
public theorem_wanted maximumLengthBoundedEdgeDisjointPathsFour_npComplete :
    fixedBoundDec 4 ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (fixedBoundDec 4)

end MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedEdgeDisjointPathsFour
