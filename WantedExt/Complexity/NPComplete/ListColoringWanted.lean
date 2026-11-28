/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LIST COLORING is NP-complete

Source:
J. Kratochvíl and Z. Tuza, "Algorithmic complexity of list colorings", Discrete Applied
Mathematics, 1994.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ListColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ListColoring

/-!
# LIST COLORING is NP-complete

An undirected graph with an explicit finite color list for every vertex. The question is
whether there is a proper coloring choosing each vertex's color from its own list.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LIST COLORING is NP-complete.** The LIST COLORING decision problem belongs to NP, and every
decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: J. Kratochvíl and Z. Tuza, "Algorithmic
complexity of list colorings", Discrete Applied Mathematics, 1994. -/
public theorem_wanted listColoring_npComplete :
    listColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L listColoringDec

end MetaMathlibExt.Complexity.NPComplete.ListColoring
