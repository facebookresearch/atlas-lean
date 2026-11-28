/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CUTTING STOCK is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR1] BIN PACKING;
F. Eisenbrand and G. Shmonin, "Carathéodory bounds for integer cones", Operations Research
Letters 34 (2006), 564-568, doi:10.1016/j.orl.2005.09.008;
M. X. Goemans and T. Rothvoss, "Polynomiality for bin packing with a constant number of item
types", Journal of the ACM 67 (2020), Article 38, doi:10.1145/3421750.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CuttingStockDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CuttingStock

/-!
# CUTTING STOCK is NP-complete

The (one-dimensional) cutting stock problem, that is, bin packing with item types: `d` item
sizes `s_1, …, s_d ∈ [0, 1]` (rationals) with multiplicities `a_1, …, a_d`, all numbers in
binary encoding, and a number `K` of bins. The question is whether the `a_j` copies of each
item of size `s_j` can be packed into `K` unit-capacity bins. This is the decision form of
problem (1) of Goemans and Rothvoss: are there at most `K` vectors `x ∈ ℤ_{≥0}^d` with
`sᵀx ≤ 1` (bin patterns, with repetition) summing to `a`?

With all multiplicities `1` it is BIN PACKING [SR1], which is strongly NP-complete, so the
problem is strongly NP-hard. Because multiplicities are encoded in binary, a packing can have
exponentially many items; NP membership follows from the Eisenbrand-Shmonin bound on the
number of distinct patterns needed in an integer conic combination.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CUTTING STOCK is NP-complete.** Source: Garey and Johnson (1979), [SR1]; Eisenbrand and
Shmonin (2006); Goemans and Rothvoss (2020). -/
public theorem_wanted cuttingStock_npComplete :
    cuttingStockDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cuttingStockDec

end MetaMathlibExt.Complexity.NPComplete.CuttingStock
