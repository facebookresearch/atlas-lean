/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROMAN DOMINATION is NP-complete

Source:
E. J. Cockayne, P. A. Dreyer Jr., S. M. Hedetniemi, and S. T. Hedetniemi, "Roman domination in
graphs", Discrete Mathematics 278 (2004), 11-22.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RomanDominationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RomanDomination

/-!
# ROMAN DOMINATION is NP-complete

An undirected graph and a bound `K`. The question is whether there is a Roman dominating
function: a labeling with values `0, 1, 2` such that every `0`-vertex has a `2`-neighbor, and
the total label weight is at most `K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ROMAN DOMINATION is NP-complete.** The decision problem ROMAN DOMINATION belongs to NP, and
every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: E. J. Cockayne, P. A. Dreyer Jr., S. M.
Hedetniemi, and S. T. Hedetniemi, "Roman domination in graphs", Discrete Mathematics 278
(2004), 11-22. -/
public theorem_wanted romanDomination_npComplete :
    romanDominationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L romanDominationDec

end MetaMathlibExt.Complexity.NPComplete.RomanDomination
