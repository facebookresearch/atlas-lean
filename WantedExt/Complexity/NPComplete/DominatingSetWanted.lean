/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), DOMINATING SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-!
# DOMINATING SET is NP-complete

An undirected graph and a bound `K`. The question is whether some set of at most `K` vertices
dominates the graph: every vertex is in the set or adjacent to a vertex in the set.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/


/-- **DOMINATING SET is NP-complete.** The decision problem DOMINATING SET belongs to NP, and
every decision problem in NP reduces to DOMINATING SET by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), DOMINATING SET. -/
public theorem_wanted dominatingSet_npComplete :
    dominatingSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSet
