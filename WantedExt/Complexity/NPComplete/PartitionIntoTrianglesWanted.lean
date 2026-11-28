/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO TRIANGLES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), PARTITION INTO TRIANGLES;
D. G. Kirkpatrick and P. Hell, "On the complexity of general graph factor problems", SIAM
Journal on Computing 12 (1983), 601-609.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PartitionIntoTrianglesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoTriangles

/-!
# PARTITION INTO TRIANGLES is NP-complete

An undirected graph. The question is whether the vertices can be partitioned into triples, each
inducing a triangle (all three pairs adjacent).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARTITION INTO TRIANGLES is NP-complete.** The decision problem PARTITION INTO TRIANGLES
lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to
PARTITION INTO TRIANGLES.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), PARTITION INTO TRIANGLES; D. G. Kirkpatrick and P.
Hell, "On the complexity of general graph factor problems", SIAM Journal on Computing 12
(1983), 601-609. -/
public theorem_wanted partitionIntoTriangles_npComplete :
    partitionIntoTrianglesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoTrianglesDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoTriangles
