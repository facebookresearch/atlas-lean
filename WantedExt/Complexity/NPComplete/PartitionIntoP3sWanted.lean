/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO PATHS OF LENGTH 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), PARTITION INTO PATHS; M.
E. Dyer and A. M. Frieze, "On the complexity of partitioning graphs into connected subgraphs",
Discrete Applied Mathematics 10 (1985), 139-153.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PartitionIntoP3sDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoP3s

/-!
# PARTITION INTO PATHS OF LENGTH 2 is NP-complete

An undirected graph. The question is whether the vertices can be partitioned into triples, each
containing a path on three vertices: two consecutive edges of the triple. The path need not be
induced: a triangle triple qualifies, using two of its three edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARTITION INTO PATHS OF LENGTH 2 is NP-complete.** The decision problem PARTITION INTO PATHS
OF LENGTH 2 belongs to NP, and every decision problem in NP has a polynomial-time many-one
reduction to it.

Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), PARTITION INTO PATHS; M. E. Dyer and A. M.
Frieze, "On the complexity of partitioning graphs into connected subgraphs", Discrete
Applied Mathematics 10 (1985), 139-153. -/
public theorem_wanted partitionIntoP3s_npComplete :
    partitionIntoP3sDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoP3sDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoP3s
