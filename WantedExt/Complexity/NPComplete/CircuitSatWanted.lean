/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CIRCUIT SAT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), CIRCUIT SATISFIABILITY; S. A. Cook, "The complexity of theorem-proving
procedures" (1971).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CircuitSatDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CircuitSat

/-!
# CIRCUIT SAT is NP-complete

A circuit is a list of gates. Gate `0` is AND, `1` is OR, `2` is NOT (second input ignored and
unconstrained), `3` is the variable with the given index, `4` is constant true, `5` is constant
false (both inputs ignored and unconstrained). A gate's used inputs refer either to a variable
index (below the number of variables) or to an earlier gate (variable count plus gate index).
The question is whether some assignment to the variables makes the output of the last gate
true. The empty circuit has no output and is a no-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CIRCUIT SAT is NP-complete.** The CIRCUIT SAT decision problem on bitstrings belongs to the
class NP, and every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability: A Guide to the Theory of NP-Completeness* (1979), CIRCUIT SATISFIABILITY;
S. A. Cook, "The complexity of theorem-proving procedures" (1971). -/
public theorem_wanted circuitSat_npComplete :
    circuitSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L circuitSatDec

end MetaMathlibExt.Complexity.NPComplete.CircuitSat
