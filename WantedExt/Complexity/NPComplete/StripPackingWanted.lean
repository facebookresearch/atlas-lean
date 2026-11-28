/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRIP PACKING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), STRIP PACKING (axis-
aligned, no rotations).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.StripPackingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StripPacking

/-!
# STRIP PACKING is NP-complete

Axis-aligned rectangles with integer dimensions, a strip of width `W`, and a height bound `H`.
The question is whether the rectangles can be placed at integer coordinates inside the strip
without overlap, with no rotations. Rectangles must have positive width and height: degenerate
zero-area items are malformed.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **STRIP PACKING is NP-complete.** The STRIP PACKING decision problem belongs to NP, and every
decision problem $L$ in NP reduces to STRIP PACKING by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), STRIP PACKING (axis-aligned, no rotations). -/
public theorem_wanted stripPacking_npComplete :
    stripPackingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L stripPackingDec

end MetaMathlibExt.Complexity.NPComplete.StripPacking
