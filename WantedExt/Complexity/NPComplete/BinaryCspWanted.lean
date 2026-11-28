/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BINARY CONSTRAINT SATISFACTION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), CONSTRAINT SATISFACTION; R. Dechter, *Constraint Processing* (2003).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BinaryCspDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BinaryCsp

/-!
# BINARY CONSTRAINT SATISFACTION is NP-complete

Variables with finite explicit domains, and binary constraints given by lists of allowed value
pairs. The question is whether there is an assignment giving every variable a value in its
domain and satisfying every constraint.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BINARY CONSTRAINT SATISFACTION is NP-complete.** The decision problem BINARY CONSTRAINT
SATISFACTION over bitstrings belongs to NP, and every decision problem in NP has a
polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability: A Guide to the Theory of NP-Completeness* (1979),
CONSTRAINT SATISFACTION; R. Dechter, *Constraint Processing* (2003). -/
public theorem_wanted binaryCsp_npComplete :
    binaryCspDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L binaryCspDec

end MetaMathlibExt.Complexity.NPComplete.BinaryCsp
