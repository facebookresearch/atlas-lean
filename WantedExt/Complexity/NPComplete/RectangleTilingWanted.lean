/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECTANGLE TILING is NP-complete

Source:
S. Khanna, S. Muthukrishnan and M. Paterson, "On approximating rectangle tiling and packing",
Proceedings of the Ninth Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 1998), 384-393
(Section 1.1, problem RTILE; Theorem 2.1: RTILE is NP-hard even with element weights that are
non-negative integers bounded by a constant, by a reduction from PLANAR-3SAT); research report
version: Department of Computer Science Research Report CS-RR-339, University of Warwick (1998);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, entry MINIMUM
RECTANGLE TILING.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RectangleTilingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RectangleTiling

/-!
# RECTANGLE TILING is NP-complete

INSTANCE: an `n × n` array `A` of non-negative numbers, a positive integer `p` and a positive
integer `K`.
QUESTION: is there a partition of `A` into at most `p` non-overlapping rectangular subarrays
(rectangles that cover `A` without overlap) such that the weight of every rectangle, the sum of
the array elements that fall within it, is at most `K`?

This is the decision version of Khanna, Muthukrishnan and Paterson's rectangle tiling problem
RTILE (Section 1.1: "Given an `n × n` array `A` of non-negative numbers, partition it into at most
`p` rectangular subarrays (that is, the rectangles cover `A` without overlap) such that the
maximum weight of any rectangle is minimized"), in the form of the Crescenzi-Kann compendium
entry MINIMUM RECTANGLE TILING (`p` and the bound `K` positive integers; the compendium writes
"a partition of `A` into `p` non-overlapping rectangular subarrays", and the primary source's "at
most `p`" is followed here). Theorem 2.1 shows that
it is NP-hard already when the elements are non-negative integers bounded by a constant (its
reduction produces instances with elements in `{1, …, 4}` and `K = 4`); here the elements are
non-negative integers. Membership in NP: a tiling assigns each of the `n²` cells one of at most
`p` rectangles, a certificate of polynomial size.

The array is given by its rows, each a list of `n` elements, where `n` is the number of rows;
cell `(r, c)` (`r, c : Fin n`) holds the `c`-th element of the `r`-th row. A partition into at most
`p` rectangles is a map `g` from the cells to `Fin p` whose classes `g⁻¹(j)` are rectangles: for
each `j` there are bounds `r₁, r₂, c₁, c₂` such that `g x = j` exactly for the cells `x` with
`r₁ ≤ x.1 ≤ r₂` and `c₁ ≤ x.2 ≤ c₂` (an unused index has an empty class). The weight of class
`j` is the sum of the elements of its cells. All numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RECTANGLE TILING is NP-complete.** Source: Khanna, Muthukrishnan and Paterson (1998),
Theorem 2.1 (hardness); the certificate of the module docstring gives membership in NP. -/
public theorem_wanted rectangleTiling_npComplete :
    rectangleTilingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rectangleTilingDec

end MetaMathlibExt.Complexity.NPComplete.RectangleTiling
