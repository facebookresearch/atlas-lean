/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM QUADRATIC ASSIGNMENT is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, MAXIMUM
QUADRATIC ASSIGNMENT;
E. M. Arkin, R. Hassin and M. Sviridenko, "Approximating the maximum quadratic assignment
problem", Information Processing Letters 77 (2001), 13-16,
doi:10.1016/S0020-0190(00)00151-4.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaximumQuadraticAssignmentDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumQuadraticAssignment

/-!
# MAXIMUM QUADRATIC ASSIGNMENT is NP-complete

INSTANCE: nonnegative symmetric `n × n` matrices `A = (a_{k,l})` and `B = (b_{i,j})`, and a
positive integer `K`. QUESTION: is there a permutation `π : [1..n] → [1..n]` such that
`∑_{i ≠ j} a_{π(i),π(j)} b_{i,j} ≥ K`?

This is the decision version of Crescenzi and Kann's MAXIMUM QUADRATIC ASSIGNMENT.
Arkin, Hassin and Sviridenko (Section 1) state that the problem, which in their version also
has a linear term `∑_i c_{i,π(i)}`, is NP-hard; the version here is theirs with `C = 0`, which
contains their special case MAX DISPERSION (`A` a clique on `p` vertices plus `n - p` isolated
vertices, Section 2): with `B` the adjacency matrix of a graph `G`, the measure is at least
`p (p - 1)` iff `G` has a clique on `p` vertices. Membership in NP: `π` is a certificate.

Indices are `0, ..., n - 1`. The instance has the shape of
`QuadraticAssignment.QuadraticAssignmentInstance`, and `WellFormed` extends that module's
well-formedness (both matrices are `n × n`) with symmetry and `0 < K`. Entries are natural
numbers, so the matrices are nonnegative. As there, a permutation is a list `perm` that is a
permutation of `[0, ..., n - 1]`, read as `π(i) = perm[i]`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM QUADRATIC ASSIGNMENT is NP-complete.** Source: Crescenzi and Kann, MAXIMUM QUADRATIC
ASSIGNMENT; Arkin, Hassin and Sviridenko (2001). -/
public theorem_wanted maximumQuadraticAssignment_npComplete :
    maximumQuadraticAssignmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumQuadraticAssignmentDec

end MetaMathlibExt.Complexity.NPComplete.MaximumQuadraticAssignment
