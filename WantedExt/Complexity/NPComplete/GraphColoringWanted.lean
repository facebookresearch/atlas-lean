/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH COLORING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), GRAPH COLORING (chromatic
number); R. M. Karp, "Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring

/-!
# GRAPH COLORING is NP-complete

An undirected graph and a bound `K`. The question is whether the chromatic number is at most
`K`: a coloring with colors `0, …, K - 1` in which adjacent vertices differ.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/


/-- **GRAPH COLORING is NP-complete.** The decision problem GRAPH COLORING belongs to NP, and
every decision problem $L$ in NP has a polynomial-time many-one reduction to GRAPH COLORING.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), GRAPH COLORING (chromatic number); R. M. Karp, "Reducibility among
combinatorial problems" (1972). -/
public theorem_wanted graphColoring_npComplete :
    graphColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphColoringDec

end MetaMathlibExt.Complexity.NPComplete.GraphColoring
